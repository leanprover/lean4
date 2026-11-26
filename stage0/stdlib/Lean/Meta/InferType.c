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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27;
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
v___x_982_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_982_, 10, v___x_980_);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1029_, lean_object* v_declHint_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_env_1035_; uint8_t v___x_1036_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_st_ref_get(v___y_1031_);
v_env_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_env_1035_);
lean_dec(v___x_1034_);
v___x_1036_ = l_Lean_Name_isAnonymous(v_declHint_1030_);
if (v___x_1036_ == 0)
{
uint8_t v_isExporting_1037_; 
v_isExporting_1037_ = lean_ctor_get_uint8(v_env_1035_, sizeof(void*)*13);
if (v_isExporting_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1030_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_msg_1029_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
lean_inc_ref(v_env_1035_);
v___x_1039_ = l_Lean_Environment_setExporting(v_env_1035_, v___x_1036_);
lean_inc(v_declHint_1030_);
lean_inc_ref(v___x_1039_);
v___x_1040_ = l_Lean_Environment_contains(v___x_1039_, v_declHint_1030_, v_isExporting_1037_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref(v___x_1039_);
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1030_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_msg_1029_);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_c_1047_; lean_object* v___x_1048_; 
v___x_1042_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1043_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1044_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1039_);
v___x_1045_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1039_);
lean_ctor_set(v___x_1045_, 1, v___x_1042_);
lean_ctor_set(v___x_1045_, 2, v___x_1043_);
lean_ctor_set(v___x_1045_, 3, v___x_1044_);
lean_inc(v_declHint_1030_);
v___x_1046_ = l_Lean_MessageData_ofConstName(v_declHint_1030_, v___x_1036_);
v_c_1047_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1047_, 0, v___x_1045_);
lean_ctor_set(v_c_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1039_, v_declHint_1030_);
lean_dec_ref(v___x_1039_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1030_);
v___x_1049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_c_1047_);
v___x_1051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_MessageData_note(v___x_1052_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_msg_1029_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
else
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1109_; 
v_val_1056_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1058_ = v___x_1048_;
v_isShared_1059_ = v_isSharedCheck_1109_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v___x_1048_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1109_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v_modules_1061_; lean_object* v_moduleNames_1062_; lean_object* v_mod_1063_; uint8_t v___x_1078_; 
v___x_1060_ = l_Lean_Environment_header(v_env_1035_);
lean_dec_ref(v_env_1035_);
v_modules_1061_ = lean_ctor_get(v___x_1060_, 3);
lean_inc_ref(v_modules_1061_);
v_moduleNames_1062_ = lean_ctor_get(v___x_1060_, 4);
lean_inc_ref(v_moduleNames_1062_);
lean_dec_ref(v___x_1060_);
v_mod_1063_ = lean_array_get(v___x_1033_, v_moduleNames_1062_, v_val_1056_);
lean_dec_ref(v_moduleNames_1062_);
v___x_1078_ = l_Lean_isPrivateName(v_declHint_1030_);
lean_dec(v_declHint_1030_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_array_get_size(v_modules_1061_);
v___x_1080_ = lean_nat_dec_lt(v_val_1056_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v_modules_1061_);
lean_dec(v_val_1056_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1081_; lean_object* v_toImport_1082_; uint8_t v_isExported_1083_; 
v___x_1081_ = lean_array_fget(v_modules_1061_, v_val_1056_);
lean_dec(v_val_1056_);
lean_dec_ref(v_modules_1061_);
v_toImport_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_toImport_1082_);
lean_dec(v___x_1081_);
v_isExported_1083_ = lean_ctor_get_uint8(v_toImport_1082_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1082_);
if (v_isExported_1083_ == 0)
{
goto v___jp_1064_;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_del_object(v___x_1058_);
v___x_1084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_c_1047_);
v___x_1086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_MessageData_ofName(v_mod_1063_);
lean_inc_ref(v___x_1088_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1088_);
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_MessageData_note(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v_msg_1029_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_modules_1061_);
lean_del_object(v___x_1058_);
lean_dec(v_val_1056_);
v___x_1098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_c_1047_);
v___x_1100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_MessageData_ofName(v_mod_1063_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_MessageData_note(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_msg_1029_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_c_1047_);
v___x_1067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_MessageData_ofName(v_mod_1063_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_MessageData_note(v___x_1072_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_msg_1029_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1074_);
v___x_1076_ = v___x_1058_;
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
lean_object* v___x_1110_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1030_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_msg_1029_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1111_, lean_object* v_declHint_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1111_, v_declHint_1112_, v___y_1113_);
lean_dec(v___y_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1116_, lean_object* v_declHint_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v___x_1123_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1116_, v_declHint_1117_, v___y_1121_);
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1128_ = l_Lean_unknownIdentifierMessageTag;
v___x_1129_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_a_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1134_, lean_object* v_declHint_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1134_, v_declHint_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1142_, lean_object* v_msg_1143_, lean_object* v_declHint_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1152_; 
v___x_1150_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1143_, v_declHint_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1142_, v_a_1151_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1153_, lean_object* v_msg_1154_, lean_object* v_declHint_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1153_, v_msg_1154_, v_declHint_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v_ref_1153_);
return v_res_1161_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1168_, lean_object* v_constName_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1175_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1176_ = 0;
lean_inc(v_constName_1169_);
v___x_1177_ = l_Lean_MessageData_ofConstName(v_constName_1169_, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1175_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1168_, v___x_1180_, v_constName_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1182_, lean_object* v_constName_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1182_, v_constName_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v_ref_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_ref_1196_; lean_object* v___x_1197_; 
v_ref_1196_ = lean_ctor_get(v___y_1193_, 2);
v___x_1197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1196_, v_constName_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_env_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = lean_st_ref_get(v___y_1209_);
v_env_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_ref(v_env_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = 0;
lean_inc(v_constName_1205_);
v___x_1214_ = l_Lean_Environment_findConstVal_x3f(v_env_1212_, v_constName_1205_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1215_;
}
else
{
lean_object* v_val_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_constName_1205_);
v_val_1216_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1214_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_val_1216_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 0);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_val_1216_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1231_, lean_object* v_us_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1238_; 
lean_inc(v_c_1231_);
v___x_1238_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1231_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_levelParams_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v_levelParams_1240_ = lean_ctor_get(v_a_1239_, 1);
v___x_1241_ = l_List_lengthTR___redArg(v_levelParams_1240_);
v___x_1242_ = l_List_lengthTR___redArg(v_us_1232_);
v___x_1243_ = lean_nat_dec_eq(v___x_1241_, v___x_1242_);
lean_dec(v___x_1242_);
lean_dec(v___x_1241_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_a_1239_);
v___x_1244_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1231_, v_us_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_c_1231_);
v___x_1245_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1239_, v_us_1232_, v_a_1236_);
return v___x_1245_;
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_us_1232_);
lean_dec(v_c_1231_);
v_a_1246_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1238_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1238_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1254_, lean_object* v_us_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1254_, v_us_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1262_, lean_object* v_constName_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_constName_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1270_, v_constName_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1278_, lean_object* v_ref_1279_, lean_object* v_constName_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1279_, v_constName_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1287_, lean_object* v_ref_1288_, lean_object* v_constName_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1287_, v_ref_1288_, v_constName_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v_ref_1288_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1296_, lean_object* v_ref_1297_, lean_object* v_msg_1298_, lean_object* v_declHint_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1297_, v_msg_1298_, v_declHint_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_ref_1307_, lean_object* v_msg_1308_, lean_object* v_declHint_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1306_, v_ref_1307_, v_msg_1308_, v_declHint_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_ref_1307_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1316_, lean_object* v_declHint_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1316_, v_declHint_1317_, v___y_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1324_, lean_object* v_declHint_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1324_, v_declHint_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1332_, lean_object* v_ref_1333_, lean_object* v_msg_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1333_, v_msg_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_ref_1342_, lean_object* v_msg_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1341_, v_ref_1342_, v_msg_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v_ref_1342_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_apply(lean_object* v_00_u03c3_1350_, lean_object* v_u_1351_){
_start:
{
lean_object* v_paramNames_1352_; lean_object* v_lvls_1353_; uint8_t v___x_1354_; 
v_paramNames_1352_ = lean_ctor_get(v_00_u03c3_1350_, 0);
lean_inc(v_paramNames_1352_);
v_lvls_1353_ = lean_ctor_get(v_00_u03c3_1350_, 1);
lean_inc(v_lvls_1353_);
lean_dec_ref(v_00_u03c3_1350_);
v___x_1354_ = l_List_isEmpty___redArg(v_paramNames_1352_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Level_instantiateParams(v_u_1351_, v_paramNames_1352_, v_lvls_1353_);
return v___x_1355_;
}
else
{
lean_dec(v_lvls_1353_);
lean_dec(v_paramNames_1352_);
return v_u_1351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_applyList(lean_object* v_00_u03c3_1356_, lean_object* v_us_1357_){
_start:
{
lean_object* v_paramNames_1358_; uint8_t v___x_1359_; 
v_paramNames_1358_ = lean_ctor_get(v_00_u03c3_1356_, 0);
v___x_1359_ = l_List_isEmpty___redArg(v_paramNames_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_LevelSubst_apply), 2, 1);
lean_closure_set(v___x_1360_, 0, v_00_u03c3_1356_);
v___x_1361_ = lean_box(0);
v___x_1362_ = l_List_mapTR_loop___redArg(v___x_1360_, v_us_1357_, v___x_1361_);
return v___x_1362_;
}
else
{
lean_dec_ref(v_00_u03c3_1356_);
return v_us_1357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(lean_object* v_c_1363_, lean_object* v_us_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; 
lean_inc(v_c_1363_);
v___x_1370_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1363_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1386_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1386_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1386_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_levelParams_1375_; lean_object* v_type_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_levelParams_1375_ = lean_ctor_get(v_a_1371_, 1);
lean_inc(v_levelParams_1375_);
v_type_1376_ = lean_ctor_get(v_a_1371_, 2);
lean_inc_ref(v_type_1376_);
lean_dec(v_a_1371_);
v___x_1377_ = l_List_lengthTR___redArg(v_levelParams_1375_);
v___x_1378_ = l_List_lengthTR___redArg(v_us_1364_);
v___x_1379_ = lean_nat_dec_eq(v___x_1377_, v___x_1378_);
lean_dec(v___x_1378_);
lean_dec(v___x_1377_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref(v_type_1376_);
lean_dec(v_levelParams_1375_);
lean_del_object(v___x_1373_);
v___x_1380_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1363_, v_us_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec(v_c_1363_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_levelParams_1375_);
lean_ctor_set(v___x_1381_, 1, v_us_1364_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_type_1376_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1382_);
v___x_1384_ = v___x_1373_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_us_1364_);
lean_dec(v_c_1363_);
v_a_1387_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1370_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1370_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy___boxed(lean_object* v_c_1395_, lean_object* v_us_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_c_1395_, v_us_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1402_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1408_ = l_Lean_stringToMessageData(v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1409_, lean_object* v_idx_1410_, lean_object* v_e_1411_, lean_object* v_a_1412_, lean_object* v_00_u03b1_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1420_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1421_ = l_Lean_mkProj(v_structName_1409_, v_idx_1410_, v_e_1411_);
v___x_1422_ = l_Lean_indentExpr(v___x_1421_);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1420_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
v___x_1426_ = l_Lean_indentExpr(v_a_1412_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1427_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1429_, lean_object* v_idx_1430_, lean_object* v_e_1431_, lean_object* v_a_1432_, lean_object* v_00_u03b1_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1429_, v_idx_1430_, v_e_1431_, v_a_1432_, v_00_u03b1_1433_, v_x_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_env_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; 
v___x_1447_ = lean_st_ref_get(v___y_1445_);
v_env_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc_ref(v_env_1448_);
lean_dec(v___x_1447_);
v___x_1449_ = 0;
lean_inc(v_constName_1441_);
v___x_1450_ = l_Lean_Environment_find_x3f(v_env_1448_, v_constName_1441_, v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1451_;
}
else
{
lean_object* v_val_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_constName_1441_);
v_val_1452_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1450_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_val_1452_);
lean_dec(v___x_1450_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 0);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_val_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1467_, lean_object* v_structName_1468_, lean_object* v_e_1469_, lean_object* v_idx_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_a_1480_; uint8_t v___x_1484_; 
v___x_1484_ = lean_nat_dec_lt(v_a_1472_, v_upperBound_1467_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_idx_1470_);
lean_dec_ref(v_e_1469_);
lean_dec(v_structName_1468_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_b_1473_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; 
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
v___x_1486_ = lean_whnf(v_b_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
if (lean_obj_tag(v_a_1487_) == 7)
{
lean_object* v_body_1488_; uint8_t v___x_1489_; 
v_body_1488_ = lean_ctor_get(v_a_1487_, 2);
lean_inc_ref(v_body_1488_);
lean_dec_ref_known(v_a_1487_, 3);
v___x_1489_ = l_Lean_Expr_hasLooseBVars(v_body_1488_);
if (v___x_1489_ == 0)
{
v_a_1480_ = v_body_1488_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_inc_ref(v_e_1469_);
lean_inc(v_a_1472_);
lean_inc(v_structName_1468_);
v___x_1490_ = l_Lean_mkProj(v_structName_1468_, v_a_1472_, v_e_1469_);
v___x_1491_ = lean_expr_instantiate1(v_body_1488_, v___x_1490_);
lean_dec_ref(v___x_1490_);
lean_dec_ref(v_body_1488_);
v_a_1480_ = v___x_1491_;
goto v___jp_1479_;
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1492_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1469_);
lean_inc(v_idx_1470_);
lean_inc(v_structName_1468_);
v___x_1493_ = l_Lean_mkProj(v_structName_1468_, v_idx_1470_, v_e_1469_);
v___x_1494_ = l_Lean_indentExpr(v___x_1493_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1492_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
lean_inc_ref(v_a_1471_);
v___x_1498_ = l_Lean_indentExpr(v_a_1471_);
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1499_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_dec_ref_known(v___x_1500_, 1);
v_a_1480_ = v_a_1487_;
goto v___jp_1479_;
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1487_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_idx_1470_);
lean_dec_ref(v_e_1469_);
lean_dec(v_structName_1468_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
else
{
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_idx_1470_);
lean_dec_ref(v_e_1469_);
lean_dec(v_structName_1468_);
return v___x_1486_;
}
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_a_1472_, v___x_1481_);
lean_dec(v_a_1472_);
v_a_1472_ = v___x_1482_;
v_b_1473_ = v_a_1480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1509_, lean_object* v_structName_1510_, lean_object* v_e_1511_, lean_object* v_idx_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1509_, v_structName_1510_, v_e_1511_, v_idx_1512_, v_a_1513_, v_a_1514_, v_b_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v_upperBound_1509_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1522_, lean_object* v_structName_1523_, lean_object* v_e_1524_, lean_object* v_idx_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_a_1535_; uint8_t v___x_1539_; 
v___x_1539_ = lean_nat_dec_lt(v_a_1527_, v_upperBound_1522_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_idx_1525_);
lean_dec_ref(v_e_1524_);
lean_dec(v_structName_1523_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_b_1528_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; 
lean_inc(v___y_1532_);
lean_inc_ref(v___y_1531_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
v___x_1541_ = lean_whnf(v_b_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
if (lean_obj_tag(v_a_1542_) == 7)
{
lean_object* v_body_1543_; uint8_t v___x_1544_; 
v_body_1543_ = lean_ctor_get(v_a_1542_, 2);
lean_inc_ref(v_body_1543_);
lean_dec_ref_known(v_a_1542_, 3);
v___x_1544_ = l_Lean_Expr_hasLooseBVars(v_body_1543_);
if (v___x_1544_ == 0)
{
v_a_1535_ = v_body_1543_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc_ref(v_e_1524_);
lean_inc(v_a_1527_);
lean_inc(v_structName_1523_);
v___x_1545_ = l_Lean_mkProj(v_structName_1523_, v_a_1527_, v_e_1524_);
v___x_1546_ = lean_expr_instantiate1(v_body_1543_, v___x_1545_);
lean_dec_ref(v___x_1545_);
lean_dec_ref(v_body_1543_);
v_a_1535_ = v___x_1546_;
goto v___jp_1534_;
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1547_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1524_);
lean_inc(v_idx_1525_);
lean_inc(v_structName_1523_);
v___x_1548_ = l_Lean_mkProj(v_structName_1523_, v_idx_1525_, v_e_1524_);
v___x_1549_ = l_Lean_indentExpr(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
lean_inc_ref(v_a_1526_);
v___x_1553_ = l_Lean_indentExpr(v_a_1526_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1554_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_dec_ref_known(v___x_1555_, 1);
v_a_1535_ = v_a_1542_;
goto v___jp_1534_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1542_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_idx_1525_);
lean_dec_ref(v_e_1524_);
lean_dec(v_structName_1523_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
else
{
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_idx_1525_);
lean_dec_ref(v_e_1524_);
lean_dec(v_structName_1523_);
return v___x_1541_;
}
}
v___jp_1534_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_add(v_a_1527_, v___x_1536_);
lean_dec(v_a_1527_);
v___x_1538_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1522_, v_structName_1523_, v_e_1524_, v_idx_1525_, v_a_1526_, v___x_1537_, v_a_1535_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1564_, lean_object* v_structName_1565_, lean_object* v_e_1566_, lean_object* v_idx_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1564_, v_structName_1565_, v_e_1566_, v_idx_1567_, v_a_1568_, v_a_1569_, v_b_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v_upperBound_1564_);
return v_res_1576_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1577_; lean_object* v_dummy_1578_; 
v___x_1577_ = lean_box(0);
v_dummy_1578_ = l_Lean_Expr_sort___override(v___x_1577_);
return v_dummy_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1579_, lean_object* v_idx_1580_, lean_object* v_e_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; 
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
lean_inc(v_a_1583_);
lean_inc_ref(v_a_1582_);
lean_inc_ref(v_e_1581_);
v___x_1587_ = lean_infer_type(v_e_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
lean_inc(v_a_1583_);
lean_inc_ref(v_a_1582_);
v___x_1589_ = lean_whnf(v_a_1588_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l_Lean_Expr_getAppFn(v_a_1590_);
if (lean_obj_tag(v___x_1591_) == 4)
{
lean_object* v_declName_1592_; lean_object* v_us_1593_; lean_object* v___x_1594_; lean_object* v_env_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; 
v_declName_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_declName_1592_);
v_us_1593_ = lean_ctor_get(v___x_1591_, 1);
lean_inc(v_us_1593_);
lean_dec_ref_known(v___x_1591_, 2);
v___x_1594_ = lean_st_ref_get(v_a_1585_);
v_env_1598_ = lean_ctor_get(v___x_1594_, 0);
lean_inc_ref(v_env_1598_);
lean_dec(v___x_1594_);
v___x_1599_ = 0;
v___x_1600_ = l_Lean_Environment_find_x3f(v_env_1598_, v_declName_1592_, v___x_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_dec(v_us_1593_);
v___x_1601_ = lean_box(0);
v___x_1602_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1601_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1602_;
}
else
{
lean_object* v_val_1603_; 
v_val_1603_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_val_1603_);
lean_dec_ref_known(v___x_1600_, 1);
if (lean_obj_tag(v_val_1603_) == 5)
{
lean_object* v_val_1604_; lean_object* v_ctors_1605_; 
v_val_1604_ = lean_ctor_get(v_val_1603_, 0);
lean_inc_ref(v_val_1604_);
lean_dec_ref_known(v_val_1603_, 1);
v_ctors_1605_ = lean_ctor_get(v_val_1604_, 4);
lean_inc(v_ctors_1605_);
if (lean_obj_tag(v_ctors_1605_) == 1)
{
lean_object* v_tail_1606_; 
v_tail_1606_ = lean_ctor_get(v_ctors_1605_, 1);
if (lean_obj_tag(v_tail_1606_) == 0)
{
lean_object* v_toConstantVal_1607_; lean_object* v_numParams_1608_; lean_object* v_numIndices_1609_; lean_object* v_head_1610_; lean_object* v___x_1611_; 
v_toConstantVal_1607_ = lean_ctor_get(v_val_1604_, 0);
lean_inc_ref(v_toConstantVal_1607_);
v_numParams_1608_ = lean_ctor_get(v_val_1604_, 1);
lean_inc(v_numParams_1608_);
v_numIndices_1609_ = lean_ctor_get(v_val_1604_, 2);
lean_inc(v_numIndices_1609_);
lean_dec_ref(v_val_1604_);
v_head_1610_ = lean_ctor_get(v_ctors_1605_, 0);
lean_inc(v_head_1610_);
lean_dec_ref_known(v_ctors_1605_, 2);
v___x_1611_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1610_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
if (lean_obj_tag(v_a_1612_) == 6)
{
lean_object* v_val_1613_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v_name_1653_; uint8_t v___x_1654_; 
v_val_1613_ = lean_ctor_get(v_a_1612_, 0);
lean_inc_ref(v_val_1613_);
lean_dec_ref_known(v_a_1612_, 1);
v_name_1653_ = lean_ctor_get(v_toConstantVal_1607_, 0);
lean_inc(v_name_1653_);
lean_dec_ref(v_toConstantVal_1607_);
v___x_1654_ = lean_name_eq(v_name_1653_, v_structName_1579_);
lean_dec(v_name_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_val_1613_);
lean_dec(v_numIndices_1609_);
lean_dec(v_numParams_1608_);
lean_dec(v_us_1593_);
v___x_1655_ = lean_box(0);
v___x_1656_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1655_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
else
{
v___y_1615_ = v_a_1582_;
v___y_1616_ = v_a_1583_;
v___y_1617_ = v_a_1584_;
v___y_1618_ = v_a_1585_;
goto v___jp_1614_;
}
v___jp_1614_:
{
lean_object* v_dummy_1619_; lean_object* v_nargs_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v_dummy_1619_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1620_ = l_Lean_Expr_getAppNumArgs(v_a_1590_);
lean_inc(v_nargs_1620_);
v___x_1621_ = lean_mk_array(v_nargs_1620_, v_dummy_1619_);
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_sub(v_nargs_1620_, v___x_1622_);
lean_dec(v_nargs_1620_);
lean_inc(v_a_1590_);
v___x_1624_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1590_, v___x_1621_, v___x_1623_);
v___x_1625_ = lean_nat_add(v_numParams_1608_, v_numIndices_1609_);
lean_dec(v_numIndices_1609_);
v___x_1626_ = lean_array_get_size(v___x_1624_);
v___x_1627_ = lean_nat_dec_eq(v___x_1625_, v___x_1626_);
lean_dec(v___x_1625_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec_ref(v___x_1624_);
lean_dec_ref(v_val_1613_);
lean_dec(v_numParams_1608_);
lean_dec(v_us_1593_);
v___x_1628_ = lean_box(0);
v___x_1629_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1628_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
return v___x_1629_;
}
else
{
lean_object* v_toConstantVal_1630_; lean_object* v_name_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_toConstantVal_1630_ = lean_ctor_get(v_val_1613_, 0);
lean_inc_ref(v_toConstantVal_1630_);
lean_dec_ref(v_val_1613_);
v_name_1631_ = lean_ctor_get(v_toConstantVal_1630_, 0);
lean_inc(v_name_1631_);
lean_dec_ref(v_toConstantVal_1630_);
v___x_1632_ = l_Lean_mkConst(v_name_1631_, v_us_1593_);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = l_Array_toSubarray___redArg(v___x_1624_, v___x_1633_, v_numParams_1608_);
v___x_1635_ = l_Subarray_copy___redArg(v___x_1634_);
v___x_1636_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1632_, v___x_1635_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec_ref(v___x_1635_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
lean_inc(v_a_1590_);
lean_inc_ref(v_e_1581_);
lean_inc(v_structName_1579_);
lean_inc(v_idx_1580_);
v___x_1638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1580_, v_structName_1579_, v_e_1581_, v_idx_1580_, v_a_1590_, v___x_1633_, v_a_1637_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
lean_inc(v___y_1618_);
lean_inc_ref(v___y_1617_);
lean_inc(v___y_1616_);
lean_inc_ref(v___y_1615_);
v___x_1640_ = lean_whnf(v_a_1639_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1652_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1652_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1652_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
if (lean_obj_tag(v_a_1641_) == 7)
{
lean_object* v_binderType_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
lean_dec(v_a_1590_);
lean_dec_ref(v_e_1581_);
lean_dec(v_idx_1580_);
lean_dec(v_structName_1579_);
v_binderType_1645_ = lean_ctor_get(v_a_1641_, 1);
lean_inc_ref(v_binderType_1645_);
lean_dec_ref_known(v_a_1641_, 3);
v___x_1646_ = lean_expr_consume_type_annotations(v_binderType_1645_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1646_);
v___x_1648_ = v___x_1643_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_del_object(v___x_1643_);
lean_dec(v_a_1641_);
v___x_1650_ = lean_box(0);
v___x_1651_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1650_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
return v___x_1651_;
}
}
}
else
{
lean_dec(v_a_1590_);
lean_dec_ref(v_e_1581_);
lean_dec(v_idx_1580_);
lean_dec(v_structName_1579_);
return v___x_1640_;
}
}
else
{
lean_dec(v_a_1590_);
lean_dec_ref(v_e_1581_);
lean_dec(v_idx_1580_);
lean_dec(v_structName_1579_);
return v___x_1638_;
}
}
else
{
lean_dec(v_a_1590_);
lean_dec_ref(v_e_1581_);
lean_dec(v_idx_1580_);
lean_dec(v_structName_1579_);
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec(v_a_1612_);
lean_dec(v_numIndices_1609_);
lean_dec(v_numParams_1608_);
lean_dec_ref(v_toConstantVal_1607_);
lean_dec(v_us_1593_);
v___x_1665_ = lean_box(0);
v___x_1666_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1665_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1666_;
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_numIndices_1609_);
lean_dec(v_numParams_1608_);
lean_dec_ref(v_toConstantVal_1607_);
lean_dec(v_us_1593_);
lean_dec(v_a_1590_);
lean_dec_ref(v_e_1581_);
lean_dec(v_idx_1580_);
lean_dec(v_structName_1579_);
v_a_1667_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1611_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1611_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1605_, 2);
lean_dec_ref(v_val_1604_);
lean_dec(v_us_1593_);
goto v___jp_1595_;
}
}
else
{
lean_dec(v_ctors_1605_);
lean_dec_ref(v_val_1604_);
lean_dec(v_us_1593_);
goto v___jp_1595_;
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec(v_val_1603_);
lean_dec(v_us_1593_);
v___x_1675_ = lean_box(0);
v___x_1676_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1675_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1676_;
}
}
v___jp_1595_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_box(0);
v___x_1597_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1596_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1597_;
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v___x_1591_);
v___x_1677_ = lean_box(0);
v___x_1678_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1579_, v_idx_1580_, v_e_1581_, v_a_1590_, lean_box(0), v___x_1677_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1678_;
}
}
else
{
lean_dec_ref(v_e_1581_);
lean_dec(v_idx_1580_);
lean_dec(v_structName_1579_);
return v___x_1589_;
}
}
else
{
lean_dec_ref(v_e_1581_);
lean_dec(v_idx_1580_);
lean_dec(v_structName_1579_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1679_, lean_object* v_idx_1680_, lean_object* v_e_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1679_, v_idx_1680_, v_e_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1688_, lean_object* v_structName_1689_, lean_object* v_e_1690_, lean_object* v_idx_1691_, lean_object* v_a_1692_, lean_object* v_inst_1693_, lean_object* v_R_1694_, lean_object* v_a_1695_, lean_object* v_b_1696_, lean_object* v_c_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1688_, v_structName_1689_, v_e_1690_, v_idx_1691_, v_a_1692_, v_a_1695_, v_b_1696_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1704_, lean_object* v_structName_1705_, lean_object* v_e_1706_, lean_object* v_idx_1707_, lean_object* v_a_1708_, lean_object* v_inst_1709_, lean_object* v_R_1710_, lean_object* v_a_1711_, lean_object* v_b_1712_, lean_object* v_c_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1704_, v_structName_1705_, v_e_1706_, v_idx_1707_, v_a_1708_, v_inst_1709_, v_R_1710_, v_a_1711_, v_b_1712_, v_c_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v_upperBound_1704_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1720_, lean_object* v_structName_1721_, lean_object* v_e_1722_, lean_object* v_idx_1723_, lean_object* v_a_1724_, lean_object* v_inst_1725_, lean_object* v_R_1726_, lean_object* v_a_1727_, lean_object* v_b_1728_, lean_object* v_c_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1720_, v_structName_1721_, v_e_1722_, v_idx_1723_, v_a_1724_, v_a_1727_, v_b_1728_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1736_, lean_object* v_structName_1737_, lean_object* v_e_1738_, lean_object* v_idx_1739_, lean_object* v_a_1740_, lean_object* v_inst_1741_, lean_object* v_R_1742_, lean_object* v_a_1743_, lean_object* v_b_1744_, lean_object* v_c_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1736_, v_structName_1737_, v_e_1738_, v_idx_1739_, v_a_1740_, v_inst_1741_, v_R_1742_, v_a_1743_, v_b_1744_, v_c_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v_upperBound_1736_);
return v_res_1751_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1761_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1762_ = l_Lean_indentExpr(v_type_1755_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1763_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1772_, lean_object* v_type_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1780_, lean_object* v_type_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1780_, v_type_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v_ks_1792_; lean_object* v_vs_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1817_; 
v_ks_1792_ = lean_ctor_get(v_x_1788_, 0);
v_vs_1793_ = lean_ctor_get(v_x_1788_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_x_1788_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1795_ = v_x_1788_;
v_isShared_1796_ = v_isSharedCheck_1817_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_vs_1793_);
lean_inc(v_ks_1792_);
lean_dec(v_x_1788_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1817_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = lean_array_get_size(v_ks_1792_);
v___x_1798_ = lean_nat_dec_lt(v_x_1789_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_x_1789_);
v___x_1799_ = lean_array_push(v_ks_1792_, v_x_1790_);
v___x_1800_ = lean_array_push(v_vs_1793_, v_x_1791_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 1, v___x_1800_);
lean_ctor_set(v___x_1795_, 0, v___x_1799_);
v___x_1802_ = v___x_1795_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
else
{
lean_object* v_k_x27_1804_; uint8_t v___x_1805_; 
v_k_x27_1804_ = lean_array_fget_borrowed(v_ks_1792_, v_x_1789_);
v___x_1805_ = l_Lean_instBEqMVarId_beq(v_x_1790_, v_k_x27_1804_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1807_; 
if (v_isShared_1796_ == 0)
{
v___x_1807_ = v___x_1795_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_ks_1792_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_vs_1793_);
v___x_1807_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = lean_nat_add(v_x_1789_, v___x_1808_);
lean_dec(v_x_1789_);
v_x_1788_ = v___x_1807_;
v_x_1789_ = v___x_1809_;
goto _start;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1812_ = lean_array_fset(v_ks_1792_, v_x_1789_, v_x_1790_);
v___x_1813_ = lean_array_fset(v_vs_1793_, v_x_1789_, v_x_1791_);
lean_dec(v_x_1789_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 1, v___x_1813_);
lean_ctor_set(v___x_1795_, 0, v___x_1812_);
v___x_1815_ = v___x_1795_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1813_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1818_, lean_object* v_k_1819_, lean_object* v_v_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1818_, v___x_1821_, v_k_1819_, v_v_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1824_, size_t v_x_1825_, size_t v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
if (lean_obj_tag(v_x_1824_) == 0)
{
lean_object* v_es_1829_; size_t v___x_1830_; size_t v___x_1831_; lean_object* v_j_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_es_1829_ = lean_ctor_get(v_x_1824_, 0);
v___x_1830_ = ((size_t)31ULL);
v___x_1831_ = lean_usize_land(v_x_1825_, v___x_1830_);
v_j_1832_ = lean_usize_to_nat(v___x_1831_);
v___x_1833_ = lean_array_get_size(v_es_1829_);
v___x_1834_ = lean_nat_dec_lt(v_j_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec(v_j_1832_);
lean_dec(v_x_1828_);
lean_dec(v_x_1827_);
return v_x_1824_;
}
else
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1873_; 
lean_inc_ref(v_es_1829_);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_x_1824_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_x_1824_, 0);
lean_dec(v_unused_1874_);
v___x_1836_ = v_x_1824_;
v_isShared_1837_ = v_isSharedCheck_1873_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v_x_1824_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1873_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_v_1838_; lean_object* v___x_1839_; lean_object* v_xs_x27_1840_; lean_object* v___y_1842_; 
v_v_1838_ = lean_array_fget(v_es_1829_, v_j_1832_);
v___x_1839_ = lean_box(0);
v_xs_x27_1840_ = lean_array_fset(v_es_1829_, v_j_1832_, v___x_1839_);
switch(lean_obj_tag(v_v_1838_))
{
case 0:
{
lean_object* v_key_1847_; lean_object* v_val_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1858_; 
v_key_1847_ = lean_ctor_get(v_v_1838_, 0);
v_val_1848_ = lean_ctor_get(v_v_1838_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_v_1838_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1850_ = v_v_1838_;
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_val_1848_);
lean_inc(v_key_1847_);
lean_dec(v_v_1838_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_instBEqMVarId_beq(v_x_1827_, v_key_1847_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_del_object(v___x_1850_);
v___x_1853_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1847_, v_val_1848_, v_x_1827_, v_x_1828_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
v___y_1842_ = v___x_1854_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1856_; 
lean_dec(v_val_1848_);
lean_dec(v_key_1847_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v_x_1828_);
lean_ctor_set(v___x_1850_, 0, v_x_1827_);
v___x_1856_ = v___x_1850_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_x_1827_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_x_1828_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v___y_1842_ = v___x_1856_;
goto v___jp_1841_;
}
}
}
}
case 1:
{
lean_object* v_node_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1871_; 
v_node_1859_ = lean_ctor_get(v_v_1838_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_v_1838_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1861_ = v_v_1838_;
v_isShared_1862_ = v_isSharedCheck_1871_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_node_1859_);
lean_dec(v_v_1838_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1871_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
size_t v___x_1863_; size_t v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1863_ = ((size_t)5ULL);
v___x_1864_ = lean_usize_shift_right(v_x_1825_, v___x_1863_);
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_x_1826_, v___x_1865_);
v___x_1867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1859_, v___x_1864_, v___x_1866_, v_x_1827_, v_x_1828_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1867_);
v___x_1869_ = v___x_1861_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
v___y_1842_ = v___x_1869_;
goto v___jp_1841_;
}
}
}
default: 
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_x_1827_);
lean_ctor_set(v___x_1872_, 1, v_x_1828_);
v___y_1842_ = v___x_1872_;
goto v___jp_1841_;
}
}
v___jp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = lean_array_fset(v_xs_x27_1840_, v_j_1832_, v___y_1842_);
lean_dec(v_j_1832_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1843_);
v___x_1845_ = v___x_1836_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
else
{
lean_object* v_ks_1875_; lean_object* v_vs_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1894_; 
v_ks_1875_ = lean_ctor_get(v_x_1824_, 0);
v_vs_1876_ = lean_ctor_get(v_x_1824_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_x_1824_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1878_ = v_x_1824_;
v_isShared_1879_ = v_isSharedCheck_1894_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_vs_1876_);
lean_inc(v_ks_1875_);
lean_dec(v_x_1824_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1894_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_ks_1875_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_vs_1876_);
v___x_1881_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v_newNode_1882_; size_t v___x_1883_; uint8_t v___x_1884_; 
v_newNode_1882_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1881_, v_x_1827_, v_x_1828_);
v___x_1883_ = ((size_t)7ULL);
v___x_1884_ = lean_usize_dec_le(v___x_1883_, v_x_1826_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1882_);
v___x_1886_ = lean_unsigned_to_nat(4u);
v___x_1887_ = lean_nat_dec_lt(v___x_1885_, v___x_1886_);
lean_dec(v___x_1885_);
if (v___x_1887_ == 0)
{
lean_object* v_ks_1888_; lean_object* v_vs_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_ks_1888_ = lean_ctor_get(v_newNode_1882_, 0);
lean_inc_ref(v_ks_1888_);
v_vs_1889_ = lean_ctor_get(v_newNode_1882_, 1);
lean_inc_ref(v_vs_1889_);
lean_dec_ref(v_newNode_1882_);
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1892_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1826_, v_ks_1888_, v_vs_1889_, v___x_1890_, v___x_1891_);
lean_dec_ref(v_vs_1889_);
lean_dec_ref(v_ks_1888_);
return v___x_1892_;
}
else
{
return v_newNode_1882_;
}
}
else
{
return v_newNode_1882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1895_, lean_object* v_keys_1896_, lean_object* v_vals_1897_, lean_object* v_i_1898_, lean_object* v_entries_1899_){
_start:
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_array_get_size(v_keys_1896_);
v___x_1901_ = lean_nat_dec_lt(v_i_1898_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_dec(v_i_1898_);
return v_entries_1899_;
}
else
{
lean_object* v_k_1902_; lean_object* v_v_1903_; uint64_t v___x_1904_; size_t v_h_1905_; size_t v___x_1906_; lean_object* v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; size_t v_h_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_k_1902_ = lean_array_fget_borrowed(v_keys_1896_, v_i_1898_);
v_v_1903_ = lean_array_fget_borrowed(v_vals_1897_, v_i_1898_);
v___x_1904_ = l_Lean_instHashableMVarId_hash(v_k_1902_);
v_h_1905_ = lean_uint64_to_usize(v___x_1904_);
v___x_1906_ = ((size_t)5ULL);
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = ((size_t)1ULL);
v___x_1909_ = lean_usize_sub(v_depth_1895_, v___x_1908_);
v___x_1910_ = lean_usize_mul(v___x_1906_, v___x_1909_);
v_h_1911_ = lean_usize_shift_right(v_h_1905_, v___x_1910_);
v___x_1912_ = lean_nat_add(v_i_1898_, v___x_1907_);
lean_dec(v_i_1898_);
lean_inc(v_v_1903_);
lean_inc(v_k_1902_);
v___x_1913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1899_, v_h_1911_, v_depth_1895_, v_k_1902_, v_v_1903_);
v_i_1898_ = v___x_1912_;
v_entries_1899_ = v___x_1913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1915_, lean_object* v_keys_1916_, lean_object* v_vals_1917_, lean_object* v_i_1918_, lean_object* v_entries_1919_){
_start:
{
size_t v_depth_boxed_1920_; lean_object* v_res_1921_; 
v_depth_boxed_1920_ = lean_unbox_usize(v_depth_1915_);
lean_dec(v_depth_1915_);
v_res_1921_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1920_, v_keys_1916_, v_vals_1917_, v_i_1918_, v_entries_1919_);
lean_dec_ref(v_vals_1917_);
lean_dec_ref(v_keys_1916_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_, lean_object* v_x_1926_){
_start:
{
size_t v_x_1151__boxed_1927_; size_t v_x_1152__boxed_1928_; lean_object* v_res_1929_; 
v_x_1151__boxed_1927_ = lean_unbox_usize(v_x_1923_);
lean_dec(v_x_1923_);
v_x_1152__boxed_1928_ = lean_unbox_usize(v_x_1924_);
lean_dec(v_x_1924_);
v_res_1929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1922_, v_x_1151__boxed_1927_, v_x_1152__boxed_1928_, v_x_1925_, v_x_1926_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1930_, lean_object* v_x_1931_, lean_object* v_x_1932_){
_start:
{
uint64_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1933_ = l_Lean_instHashableMVarId_hash(v_x_1931_);
v___x_1934_ = lean_uint64_to_usize(v___x_1933_);
v___x_1935_ = ((size_t)1ULL);
v___x_1936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1930_, v___x_1934_, v___x_1935_, v_x_1931_, v_x_1932_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1937_, lean_object* v_val_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v_mctx_1942_; lean_object* v_cache_1943_; lean_object* v_zetaDeltaFVarIds_1944_; lean_object* v_postponed_1945_; lean_object* v_diag_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1975_; 
v___x_1941_ = lean_st_ref_take(v___y_1939_);
v_mctx_1942_ = lean_ctor_get(v___x_1941_, 0);
v_cache_1943_ = lean_ctor_get(v___x_1941_, 1);
v_zetaDeltaFVarIds_1944_ = lean_ctor_get(v___x_1941_, 2);
v_postponed_1945_ = lean_ctor_get(v___x_1941_, 3);
v_diag_1946_ = lean_ctor_get(v___x_1941_, 4);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1948_ = v___x_1941_;
v_isShared_1949_ = v_isSharedCheck_1975_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_diag_1946_);
lean_inc(v_postponed_1945_);
lean_inc(v_zetaDeltaFVarIds_1944_);
lean_inc(v_cache_1943_);
lean_inc(v_mctx_1942_);
lean_dec(v___x_1941_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1975_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_depth_1950_; lean_object* v_levelAssignDepth_1951_; lean_object* v_lmvarCounter_1952_; lean_object* v_mvarCounter_1953_; lean_object* v_lDecls_1954_; lean_object* v_decls_1955_; lean_object* v_userNames_1956_; lean_object* v_lAssignment_1957_; lean_object* v_eAssignment_1958_; lean_object* v_dAssignment_1959_; lean_object* v_instanceTypedMVars_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1974_; 
v_depth_1950_ = lean_ctor_get(v_mctx_1942_, 0);
v_levelAssignDepth_1951_ = lean_ctor_get(v_mctx_1942_, 1);
v_lmvarCounter_1952_ = lean_ctor_get(v_mctx_1942_, 2);
v_mvarCounter_1953_ = lean_ctor_get(v_mctx_1942_, 3);
v_lDecls_1954_ = lean_ctor_get(v_mctx_1942_, 4);
v_decls_1955_ = lean_ctor_get(v_mctx_1942_, 5);
v_userNames_1956_ = lean_ctor_get(v_mctx_1942_, 6);
v_lAssignment_1957_ = lean_ctor_get(v_mctx_1942_, 7);
v_eAssignment_1958_ = lean_ctor_get(v_mctx_1942_, 8);
v_dAssignment_1959_ = lean_ctor_get(v_mctx_1942_, 9);
v_instanceTypedMVars_1960_ = lean_ctor_get(v_mctx_1942_, 10);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_mctx_1942_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1962_ = v_mctx_1942_;
v_isShared_1963_ = v_isSharedCheck_1974_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_instanceTypedMVars_1960_);
lean_inc(v_dAssignment_1959_);
lean_inc(v_eAssignment_1958_);
lean_inc(v_lAssignment_1957_);
lean_inc(v_userNames_1956_);
lean_inc(v_decls_1955_);
lean_inc(v_lDecls_1954_);
lean_inc(v_mvarCounter_1953_);
lean_inc(v_lmvarCounter_1952_);
lean_inc(v_levelAssignDepth_1951_);
lean_inc(v_depth_1950_);
lean_dec(v_mctx_1942_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1974_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1964_ = lean_box(0);
v___x_1965_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1958_, v_mvarId_1937_, v_val_1938_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 8, v___x_1965_);
v___x_1967_ = v___x_1962_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_depth_1950_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_levelAssignDepth_1951_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_lmvarCounter_1952_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_mvarCounter_1953_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_lDecls_1954_);
lean_ctor_set(v_reuseFailAlloc_1973_, 5, v_decls_1955_);
lean_ctor_set(v_reuseFailAlloc_1973_, 6, v_userNames_1956_);
lean_ctor_set(v_reuseFailAlloc_1973_, 7, v_lAssignment_1957_);
lean_ctor_set(v_reuseFailAlloc_1973_, 8, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1973_, 9, v_dAssignment_1959_);
lean_ctor_set(v_reuseFailAlloc_1973_, 10, v_instanceTypedMVars_1960_);
v___x_1967_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1967_);
v___x_1969_ = v___x_1948_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_cache_1943_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_zetaDeltaFVarIds_1944_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_postponed_1945_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_diag_1946_);
v___x_1969_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_st_ref_put(v___y_1939_, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1964_);
return v___x_1971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1976_, lean_object* v_val_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1976_, v_val_1977_, v___y_1978_);
lean_dec(v___y_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1987_; 
lean_inc(v_a_1985_);
lean_inc_ref(v_a_1984_);
lean_inc(v_a_1983_);
lean_inc_ref(v_a_1982_);
lean_inc_ref(v_type_1981_);
v___x_1987_ = lean_infer_type(v_type_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1989_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = l_Lean_Meta_whnfD(v_a_1988_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2024_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2024_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2024_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
switch(lean_obj_tag(v_a_1990_))
{
case 3:
{
lean_object* v_u_1994_; lean_object* v___x_1996_; 
lean_dec_ref(v_type_1981_);
v_u_1994_ = lean_ctor_get(v_a_1990_, 0);
lean_inc(v_u_1994_);
lean_dec_ref_known(v_a_1990_, 1);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v_u_1994_);
v___x_1996_ = v___x_1992_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_u_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
case 2:
{
lean_object* v_mvarId_1998_; lean_object* v___x_1999_; 
lean_del_object(v___x_1992_);
v_mvarId_1998_ = lean_ctor_get(v_a_1990_, 0);
lean_inc_n(v_mvarId_1998_, 2);
lean_dec_ref_known(v_a_1990_, 1);
v___x_1999_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1998_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; uint8_t v___x_2001_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = lean_unbox(v_a_2000_);
lean_dec(v_a_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec_ref(v_type_1981_);
v___x_2002_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_n(v_a_2003_, 2);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l_Lean_mkSort(v_a_2003_);
v___x_2005_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1998_, v___x_2004_, v_a_1983_);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_2005_, 0);
lean_dec(v_unused_2013_);
v___x_2007_ = v___x_2005_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_dec(v___x_2005_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v_a_2003_);
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2003_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_dec(v_mvarId_1998_);
return v___x_2002_;
}
}
else
{
lean_object* v___x_2014_; 
lean_dec(v_mvarId_1998_);
v___x_2014_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
return v___x_2014_;
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_mvarId_1998_);
lean_dec_ref(v_type_1981_);
v_a_2015_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1999_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1999_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
default: 
{
lean_object* v___x_2023_; 
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
v___x_2023_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v_type_1981_);
v_a_2025_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1989_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1989_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec_ref(v_type_1981_);
v_a_2033_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1987_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1987_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_getLevel(v_type_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_2048_, lean_object* v_val_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2048_, v_val_2049_, v___y_2051_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_2056_, lean_object* v_val_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_2056_, v_val_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2065_, v_x_2066_, v_x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2069_, lean_object* v_x_2070_, size_t v_x_2071_, size_t v_x_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2070_, v_x_2071_, v_x_2072_, v_x_2073_, v_x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
size_t v_x_1500__boxed_2082_; size_t v_x_1501__boxed_2083_; lean_object* v_res_2084_; 
v_x_1500__boxed_2082_ = lean_unbox_usize(v_x_2078_);
lean_dec(v_x_2078_);
v_x_1501__boxed_2083_ = lean_unbox_usize(v_x_2079_);
lean_dec(v_x_2079_);
v_res_2084_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2076_, v_x_2077_, v_x_1500__boxed_2082_, v_x_1501__boxed_2083_, v_x_2080_, v_x_2081_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2085_, lean_object* v_n_2086_, lean_object* v_k_2087_, lean_object* v_v_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2086_, v_k_2087_, v_v_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2090_, size_t v_depth_2091_, lean_object* v_keys_2092_, lean_object* v_vals_2093_, lean_object* v_heq_2094_, lean_object* v_i_2095_, lean_object* v_entries_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2091_, v_keys_2092_, v_vals_2093_, v_i_2095_, v_entries_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2098_, lean_object* v_depth_2099_, lean_object* v_keys_2100_, lean_object* v_vals_2101_, lean_object* v_heq_2102_, lean_object* v_i_2103_, lean_object* v_entries_2104_){
_start:
{
size_t v_depth_boxed_2105_; lean_object* v_res_2106_; 
v_depth_boxed_2105_ = lean_unbox_usize(v_depth_2099_);
lean_dec(v_depth_2099_);
v_res_2106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2098_, v_depth_boxed_2105_, v_keys_2100_, v_vals_2101_, v_heq_2102_, v_i_2103_, v_entries_2104_);
lean_dec_ref(v_vals_2101_);
lean_dec_ref(v_keys_2100_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2107_, lean_object* v_x_2108_, lean_object* v_x_2109_, lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2108_, v_x_2109_, v_x_2110_, v_x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2113_, lean_object* v_b_2114_, lean_object* v_c_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
v___x_2121_ = lean_apply_7(v_k_2113_, v_b_2114_, v_c_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, lean_box(0));
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2122_, lean_object* v_b_2123_, lean_object* v_c_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2122_, v_b_2123_, v_c_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2131_, lean_object* v_k_2132_, uint8_t v_cleanupAnnotations_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___f_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2139_, 0, v_k_2132_);
v___x_2140_ = 0;
v___x_2141_ = lean_box(0);
v___x_2142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2140_, v___x_2141_, v_type_2131_, v___f_2139_, v_cleanupAnnotations_2133_, v___x_2140_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_a_2151_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2142_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2142_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2159_, lean_object* v_k_2160_, lean_object* v_cleanupAnnotations_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2167_; lean_object* v_res_2168_; 
v_cleanupAnnotations_boxed_2167_ = lean_unbox(v_cleanupAnnotations_2161_);
v_res_2168_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2159_, v_k_2160_, v_cleanupAnnotations_boxed_2167_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2169_, lean_object* v_type_2170_, lean_object* v_k_2171_, uint8_t v_cleanupAnnotations_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2170_, v_k_2171_, v_cleanupAnnotations_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_type_2180_, lean_object* v_k_2181_, lean_object* v_cleanupAnnotations_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2188_; lean_object* v_res_2189_; 
v_cleanupAnnotations_boxed_2188_ = lean_unbox(v_cleanupAnnotations_2182_);
v_res_2189_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2179_, v_type_2180_, v_k_2181_, v_cleanupAnnotations_boxed_2188_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2190_, size_t v_i_2191_, size_t v_stop_2192_, lean_object* v_b_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_usize_dec_eq(v_i_2191_, v_stop_2192_);
if (v___x_2199_ == 0)
{
size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = ((size_t)1ULL);
v___x_2201_ = lean_usize_sub(v_i_2191_, v___x_2200_);
v___x_2202_ = lean_array_uget_borrowed(v_as_2190_, v___x_2201_);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
lean_inc(v___x_2202_);
v___x_2203_ = lean_infer_type(v___x_2202_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = l_Lean_Meta_getLevel(v_a_2204_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = l_Lean_mkLevelIMax_x27(v_a_2206_, v_b_2193_);
v_i_2191_ = v___x_2201_;
v_b_2193_ = v___x_2207_;
goto _start;
}
else
{
lean_dec(v_b_2193_);
return v___x_2205_;
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_b_2193_);
v_a_2209_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2203_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2203_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_b_2193_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2218_, lean_object* v_i_2219_, lean_object* v_stop_2220_, lean_object* v_b_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
size_t v_i_boxed_2227_; size_t v_stop_boxed_2228_; lean_object* v_res_2229_; 
v_i_boxed_2227_ = lean_unbox_usize(v_i_2219_);
lean_dec(v_i_2219_);
v_stop_boxed_2228_ = lean_unbox_usize(v_stop_2220_);
lean_dec(v_stop_2220_);
v_res_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2218_, v_i_boxed_2227_, v_stop_boxed_2228_, v_b_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v_as_2218_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2230_, lean_object* v_e_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_a_2238_; lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Meta_getLevel(v_e_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2242_, 1);
v___x_2244_ = lean_array_get_size(v_xs_2230_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_nat_dec_lt(v___x_2245_, v___x_2244_);
if (v___x_2246_ == 0)
{
v_a_2238_ = v_a_2243_;
goto v___jp_2237_;
}
else
{
size_t v___x_2247_; size_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_usize_of_nat(v___x_2244_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2230_, v___x_2247_, v___x_2248_, v_a_2243_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v_a_2238_ = v_a_2250_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2249_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2249_);
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
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2242_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2242_);
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
v___jp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = l_Lean_Level_normalize(v_a_2238_);
lean_dec(v_a_2238_);
v___x_2240_ = l_Lean_mkSort(v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2267_, lean_object* v_e_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2267_, v_e_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_xs_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___f_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; 
v___f_2282_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2283_ = 0;
v___x_2284_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2276_, v___f_2282_, v___x_2283_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2292_, lean_object* v_k_2293_, uint8_t v_cleanupAnnotations_2294_, uint8_t v_preserveNondepLet_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___f_2301_; uint8_t v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2301_, 0, v_k_2293_);
v___x_2302_ = 1;
v___x_2303_ = 0;
v___x_2304_ = lean_box(0);
v___x_2305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2292_, v___x_2302_, v___x_2302_, v_preserveNondepLet_2295_, v___x_2303_, v___x_2304_, v___f_2301_, v_cleanupAnnotations_2294_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2314_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2305_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2305_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2322_, lean_object* v_k_2323_, lean_object* v_cleanupAnnotations_2324_, lean_object* v_preserveNondepLet_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2331_; uint8_t v_preserveNondepLet_boxed_2332_; lean_object* v_res_2333_; 
v_cleanupAnnotations_boxed_2331_ = lean_unbox(v_cleanupAnnotations_2324_);
v_preserveNondepLet_boxed_2332_ = lean_unbox(v_preserveNondepLet_2325_);
v_res_2333_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2322_, v_k_2323_, v_cleanupAnnotations_boxed_2331_, v_preserveNondepLet_boxed_2332_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2334_, lean_object* v_e_2335_, lean_object* v_k_2336_, uint8_t v_cleanupAnnotations_2337_, uint8_t v_preserveNondepLet_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2335_, v_k_2336_, v_cleanupAnnotations_2337_, v_preserveNondepLet_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2345_, lean_object* v_e_2346_, lean_object* v_k_2347_, lean_object* v_cleanupAnnotations_2348_, lean_object* v_preserveNondepLet_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2355_; uint8_t v_preserveNondepLet_boxed_2356_; lean_object* v_res_2357_; 
v_cleanupAnnotations_boxed_2355_ = lean_unbox(v_cleanupAnnotations_2348_);
v_preserveNondepLet_boxed_2356_ = lean_unbox(v_preserveNondepLet_2349_);
v_res_2357_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2345_, v_e_2346_, v_k_2347_, v_cleanupAnnotations_boxed_2355_, v_preserveNondepLet_boxed_2356_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2358_, lean_object* v_e_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
lean_inc(v___y_2363_);
lean_inc_ref(v___y_2362_);
lean_inc(v___y_2361_);
lean_inc_ref(v___y_2360_);
v___x_2365_ = lean_infer_type(v_e_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; uint8_t v___x_2367_; uint8_t v___x_2368_; uint8_t v___x_2369_; lean_object* v___x_2370_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2367_ = 0;
v___x_2368_ = 1;
v___x_2369_ = 1;
v___x_2370_ = l_Lean_Meta_mkForallFVars(v_xs_2358_, v_a_2366_, v___x_2367_, v___x_2368_, v___x_2367_, v___x_2369_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2370_;
}
else
{
return v___x_2365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2371_, lean_object* v_e_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2371_, v_e_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v_xs_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___f_2386_; uint8_t v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; 
v___f_2386_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2387_ = 0;
v___x_2388_ = 1;
v___x_2389_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2380_, v___f_2386_, v___x_2387_, v___x_2388_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2396_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2399_ = l_Lean_stringToMessageData(v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2402_ = l_Lean_stringToMessageData(v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2409_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2410_ = l_Lean_MessageData_ofName(v_mvarId_2403_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2413_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2422_, lean_object* v_mvarId_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2430_, lean_object* v_mvarId_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2430_, v_mvarId_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2444_; lean_object* v_mctx_2445_; lean_object* v___x_2446_; 
v___x_2444_ = lean_st_ref_get(v_a_2440_);
v_mctx_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc_ref(v_mctx_2445_);
lean_dec(v___x_2444_);
v___x_2446_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2445_, v_mvarId_2438_);
lean_dec_ref(v_mctx_2445_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2447_;
}
else
{
lean_object* v_val_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_mvarId_2438_);
v_val_2448_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2450_ = v___x_2446_;
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_val_2448_);
lean_dec(v___x_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_type_2452_; lean_object* v___x_2454_; 
v_type_2452_ = lean_ctor_get(v_val_2448_, 2);
lean_inc_ref(v_type_2452_);
lean_dec(v_val_2448_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 0);
lean_ctor_set(v___x_2450_, 0, v_type_2452_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_type_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_lctx_2469_; lean_object* v___x_2470_; 
v_lctx_2469_ = lean_ctor_get(v_a_2465_, 2);
lean_inc(v_fvarId_2464_);
lean_inc_ref(v_lctx_2469_);
v___x_2470_ = lean_local_ctx_find(v_lctx_2469_, v_fvarId_2464_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2464_, v_a_2466_, v_a_2467_);
return v___x_2471_;
}
else
{
lean_object* v_val_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_fvarId_2464_);
v_val_2472_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2474_ = v___x_2470_;
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_val_2472_);
lean_dec(v___x_2470_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = l_Lean_LocalDecl_type(v_val_2472_);
lean_dec(v_val_2472_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2476_);
v___x_2478_ = v___x_2474_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2487_, v_a_2488_, v_a_2490_, v_a_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0(lean_object* v_a_2501_, lean_object* v_b_2502_){
_start:
{
lean_object* v_expr_2503_; uint64_t v_configKey_2504_; lean_object* v_expr_2505_; uint64_t v_configKey_2506_; uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v___x_2509_; uint64_t v___x_2510_; uint8_t v___x_2511_; 
v_expr_2503_ = lean_ctor_get(v_a_2501_, 0);
v_configKey_2504_ = lean_ctor_get_uint64(v_a_2501_, sizeof(void*)*1);
v_expr_2505_ = lean_ctor_get(v_b_2502_, 0);
v_configKey_2506_ = lean_ctor_get_uint64(v_b_2502_, sizeof(void*)*1);
v___x_2507_ = l_Lean_Expr_hash(v_expr_2503_);
v___x_2508_ = lean_uint64_mix_hash(v___x_2507_, v_configKey_2504_);
v___x_2509_ = l_Lean_Expr_hash(v_expr_2505_);
v___x_2510_ = lean_uint64_mix_hash(v___x_2509_, v_configKey_2506_);
v___x_2511_ = lean_uint64_dec_eq(v___x_2508_, v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0___boxed(lean_object* v_a_2512_, lean_object* v_b_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lam__0(v_a_2512_, v_b_2513_);
lean_dec_ref(v_b_2513_);
lean_dec_ref(v_a_2512_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_instMonadEIO___redArg();
return v___x_2516_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2518_ = l_StateRefT_x27_instMonad___redArg(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_instMonadExceptOfEIO___redArg();
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___f_2523_; 
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2523_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2523_, 0, v___x_2522_);
return v___f_2523_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___f_2525_; 
v___x_2524_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2525_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2525_, 0, v___x_2524_);
return v___f_2525_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; 
v___f_2526_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2527_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___f_2527_);
lean_ctor_set(v___x_2528_, 1, v___f_2526_);
return v___x_2528_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___f_2530_; 
v___x_2529_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2530_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2530_, 0, v___x_2529_);
return v___f_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___f_2532_; 
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2532_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2532_, 0, v___x_2531_);
return v___f_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; 
v___f_2533_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2534_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___f_2534_);
lean_ctor_set(v___x_2535_, 1, v___f_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2538_, lean_object* v_inferType_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
uint8_t v_cacheInferType_2584_; 
v_cacheInferType_2584_ = lean_ctor_get_uint8(v_a_2540_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2584_ == 0)
{
lean_dec_ref(v_e_2538_);
goto v___jp_2545_;
}
else
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_Expr_hasMVar(v_e_2538_);
if (v___x_2585_ == 0)
{
lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___f_2586_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2587_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2588_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2538_, v_a_2540_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2716_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2716_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2716_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2670_; lean_object* v_cache_2671_; lean_object* v_inferType_2672_; lean_object* v___x_2673_; 
v___x_2670_ = lean_st_ref_get(v_a_2541_);
v_cache_2671_ = lean_ctor_get(v___x_2670_, 1);
lean_inc_ref(v_cache_2671_);
lean_dec(v___x_2670_);
v_inferType_2672_ = lean_ctor_get(v_cache_2671_, 0);
lean_inc_ref(v_inferType_2672_);
lean_dec_ref(v_cache_2671_);
lean_inc(v_a_2589_);
v___x_2673_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_2586_, v___x_2587_, v_inferType_2672_, v_a_2589_);
if (lean_obj_tag(v___x_2673_) == 1)
{
lean_object* v_val_2674_; lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v_expr_2677_; uint64_t v_configKey_2678_; lean_object* v_expr_2679_; uint64_t v_configKey_2680_; uint8_t v___x_2681_; 
v_val_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_val_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v_fst_2675_ = lean_ctor_get(v_val_2674_, 0);
lean_inc(v_fst_2675_);
v_snd_2676_ = lean_ctor_get(v_val_2674_, 1);
lean_inc(v_snd_2676_);
lean_dec(v_val_2674_);
v_expr_2677_ = lean_ctor_get(v_a_2589_, 0);
v_configKey_2678_ = lean_ctor_get_uint64(v_a_2589_, sizeof(void*)*1);
v_expr_2679_ = lean_ctor_get(v_fst_2675_, 0);
lean_inc_ref(v_expr_2679_);
v_configKey_2680_ = lean_ctor_get_uint64(v_fst_2675_, sizeof(void*)*1);
lean_dec(v_fst_2675_);
v___x_2681_ = lean_uint64_dec_eq(v_configKey_2678_, v_configKey_2680_);
if (v___x_2681_ == 0)
{
lean_dec_ref(v_expr_2679_);
lean_dec(v_snd_2676_);
lean_dec_ref(v_inferType_2672_);
lean_del_object(v___x_2591_);
goto v___jp_2634_;
}
else
{
size_t v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = ((size_t)64ULL);
v___x_2683_ = lean_expr_equal_budgeted(v_expr_2677_, v_expr_2679_, v___x_2682_);
lean_dec_ref(v_expr_2679_);
switch(v___x_2683_)
{
case 0:
{
lean_dec(v_snd_2676_);
lean_dec_ref(v_inferType_2672_);
lean_del_object(v___x_2591_);
goto v___jp_2634_;
}
case 1:
{
lean_object* v___x_2685_; 
lean_dec_ref(v_inferType_2672_);
lean_dec(v_a_2589_);
lean_dec_ref(v_inferType_2539_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_snd_2676_);
v___x_2685_ = v___x_2591_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_snd_2676_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
default: 
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v_cache_2689_; lean_object* v_mctx_2690_; lean_object* v_zetaDeltaFVarIds_2691_; lean_object* v_postponed_2692_; lean_object* v_diag_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2715_; 
lean_dec(v_snd_2676_);
lean_del_object(v___x_2591_);
lean_inc(v_a_2589_);
v___x_2687_ = l_Lean_PersistentHashMap_erase___redArg(v___f_2586_, v___x_2587_, v_inferType_2672_, v_a_2589_);
v___x_2688_ = lean_st_ref_take(v_a_2541_);
v_cache_2689_ = lean_ctor_get(v___x_2688_, 1);
v_mctx_2690_ = lean_ctor_get(v___x_2688_, 0);
v_zetaDeltaFVarIds_2691_ = lean_ctor_get(v___x_2688_, 2);
v_postponed_2692_ = lean_ctor_get(v___x_2688_, 3);
v_diag_2693_ = lean_ctor_get(v___x_2688_, 4);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2695_ = v___x_2688_;
v_isShared_2696_ = v_isSharedCheck_2715_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_diag_2693_);
lean_inc(v_postponed_2692_);
lean_inc(v_zetaDeltaFVarIds_2691_);
lean_inc(v_cache_2689_);
lean_inc(v_mctx_2690_);
lean_dec(v___x_2688_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2715_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v_funInfo_2697_; lean_object* v_synthInstance_2698_; lean_object* v_whnf_2699_; lean_object* v_defEqTrans_2700_; lean_object* v_defEqPerm_2701_; lean_object* v_unfold_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2713_; 
v_funInfo_2697_ = lean_ctor_get(v_cache_2689_, 1);
v_synthInstance_2698_ = lean_ctor_get(v_cache_2689_, 2);
v_whnf_2699_ = lean_ctor_get(v_cache_2689_, 3);
v_defEqTrans_2700_ = lean_ctor_get(v_cache_2689_, 4);
v_defEqPerm_2701_ = lean_ctor_get(v_cache_2689_, 5);
v_unfold_2702_ = lean_ctor_get(v_cache_2689_, 6);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_cache_2689_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; 
v_unused_2714_ = lean_ctor_get(v_cache_2689_, 0);
lean_dec(v_unused_2714_);
v___x_2704_ = v_cache_2689_;
v_isShared_2705_ = v_isSharedCheck_2713_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_unfold_2702_);
lean_inc(v_defEqPerm_2701_);
lean_inc(v_defEqTrans_2700_);
lean_inc(v_whnf_2699_);
lean_inc(v_synthInstance_2698_);
lean_inc(v_funInfo_2697_);
lean_dec(v_cache_2689_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2713_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2687_);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_funInfo_2697_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_synthInstance_2698_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_whnf_2699_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v_defEqTrans_2700_);
lean_ctor_set(v_reuseFailAlloc_2712_, 5, v_defEqPerm_2701_);
lean_ctor_set(v_reuseFailAlloc_2712_, 6, v_unfold_2702_);
v___x_2707_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2709_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 1, v___x_2707_);
v___x_2709_ = v___x_2695_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_mctx_2690_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_zetaDeltaFVarIds_2691_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_postponed_2692_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_diag_2693_);
v___x_2709_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_st_ref_put(v_a_2541_, v___x_2709_);
goto v___jp_2634_;
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
lean_dec(v___x_2673_);
lean_dec_ref(v_inferType_2672_);
lean_del_object(v___x_2591_);
goto v___jp_2634_;
}
v___jp_2593_:
{
lean_object* v___x_2594_; 
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
lean_inc(v_a_2541_);
lean_inc_ref(v_a_2540_);
v___x_2594_ = lean_apply_5(v_inferType_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, lean_box(0));
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; uint8_t v___x_2596_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
v___x_2596_ = l_Lean_Expr_hasMVar(v_a_2595_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2632_; 
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v___x_2594_, 0);
lean_dec(v_unused_2633_);
v___x_2598_ = v___x_2594_;
v_isShared_2599_ = v_isSharedCheck_2632_;
goto v_resetjp_2597_;
}
else
{
lean_dec(v___x_2594_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2632_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v_cache_2601_; lean_object* v_mctx_2602_; lean_object* v_zetaDeltaFVarIds_2603_; lean_object* v_postponed_2604_; lean_object* v_diag_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2631_; 
v___x_2600_ = lean_st_ref_take(v_a_2541_);
v_cache_2601_ = lean_ctor_get(v___x_2600_, 1);
v_mctx_2602_ = lean_ctor_get(v___x_2600_, 0);
v_zetaDeltaFVarIds_2603_ = lean_ctor_get(v___x_2600_, 2);
v_postponed_2604_ = lean_ctor_get(v___x_2600_, 3);
v_diag_2605_ = lean_ctor_get(v___x_2600_, 4);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2607_ = v___x_2600_;
v_isShared_2608_ = v_isSharedCheck_2631_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_diag_2605_);
lean_inc(v_postponed_2604_);
lean_inc(v_zetaDeltaFVarIds_2603_);
lean_inc(v_cache_2601_);
lean_inc(v_mctx_2602_);
lean_dec(v___x_2600_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2631_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_inferType_2609_; lean_object* v_funInfo_2610_; lean_object* v_synthInstance_2611_; lean_object* v_whnf_2612_; lean_object* v_defEqTrans_2613_; lean_object* v_defEqPerm_2614_; lean_object* v_unfold_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2630_; 
v_inferType_2609_ = lean_ctor_get(v_cache_2601_, 0);
v_funInfo_2610_ = lean_ctor_get(v_cache_2601_, 1);
v_synthInstance_2611_ = lean_ctor_get(v_cache_2601_, 2);
v_whnf_2612_ = lean_ctor_get(v_cache_2601_, 3);
v_defEqTrans_2613_ = lean_ctor_get(v_cache_2601_, 4);
v_defEqPerm_2614_ = lean_ctor_get(v_cache_2601_, 5);
v_unfold_2615_ = lean_ctor_get(v_cache_2601_, 6);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_cache_2601_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2617_ = v_cache_2601_;
v_isShared_2618_ = v_isSharedCheck_2630_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_unfold_2615_);
lean_inc(v_defEqPerm_2614_);
lean_inc(v_defEqTrans_2613_);
lean_inc(v_whnf_2612_);
lean_inc(v_synthInstance_2611_);
lean_inc(v_funInfo_2610_);
lean_inc(v_inferType_2609_);
lean_dec(v_cache_2601_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2630_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_inc(v_a_2595_);
v___x_2619_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2586_, v___x_2587_, v_inferType_2609_, v_a_2589_, v_a_2595_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_funInfo_2610_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_synthInstance_2611_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v_whnf_2612_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_defEqTrans_2613_);
lean_ctor_set(v_reuseFailAlloc_2629_, 5, v_defEqPerm_2614_);
lean_ctor_set(v_reuseFailAlloc_2629_, 6, v_unfold_2615_);
v___x_2621_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 1, v___x_2621_);
v___x_2623_ = v___x_2607_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_mctx_2602_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v_zetaDeltaFVarIds_2603_);
lean_ctor_set(v_reuseFailAlloc_2628_, 3, v_postponed_2604_);
lean_ctor_set(v_reuseFailAlloc_2628_, 4, v_diag_2605_);
v___x_2623_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_st_ref_put(v_a_2541_, v___x_2623_);
if (v_isShared_2599_ == 0)
{
v___x_2626_ = v___x_2598_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2595_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2595_);
lean_dec(v_a_2589_);
return v___x_2594_;
}
}
else
{
lean_dec(v_a_2589_);
return v___x_2594_;
}
}
v___jp_2634_:
{
lean_object* v___x_2635_; lean_object* v_toApplicative_2636_; lean_object* v_toFunctor_2637_; lean_object* v_toSeq_2638_; lean_object* v_toSeqLeft_2639_; lean_object* v_toSeqRight_2640_; lean_object* v___f_2641_; lean_object* v___f_2642_; lean_object* v___f_2643_; lean_object* v___f_2644_; lean_object* v___x_2645_; lean_object* v___f_2646_; lean_object* v___f_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_toCold_2656_; lean_object* v_cancelTk_x3f_2657_; 
v___x_2635_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2636_ = lean_ctor_get(v___x_2635_, 0);
v_toFunctor_2637_ = lean_ctor_get(v_toApplicative_2636_, 0);
v_toSeq_2638_ = lean_ctor_get(v_toApplicative_2636_, 2);
v_toSeqLeft_2639_ = lean_ctor_get(v_toApplicative_2636_, 3);
v_toSeqRight_2640_ = lean_ctor_get(v_toApplicative_2636_, 4);
v___f_2641_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2642_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2637_, 2);
v___f_2643_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2643_, 0, v_toFunctor_2637_);
v___f_2644_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2644_, 0, v_toFunctor_2637_);
v___x_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___f_2643_);
lean_ctor_set(v___x_2645_, 1, v___f_2644_);
lean_inc(v_toSeqRight_2640_);
v___f_2646_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2646_, 0, v_toSeqRight_2640_);
lean_inc(v_toSeqLeft_2639_);
v___f_2647_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2647_, 0, v_toSeqLeft_2639_);
lean_inc(v_toSeq_2638_);
v___f_2648_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2648_, 0, v_toSeq_2638_);
v___x_2649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2645_);
lean_ctor_set(v___x_2649_, 1, v___f_2641_);
lean_ctor_set(v___x_2649_, 2, v___f_2648_);
lean_ctor_set(v___x_2649_, 3, v___f_2647_);
lean_ctor_set(v___x_2649_, 4, v___f_2646_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v___f_2642_);
v___x_2651_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2652_ = l_Lean_Core_instMonadRefCoreM;
v___x_2653_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2654_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2653_, v___x_2650_);
v___x_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2651_);
lean_ctor_set(v___x_2655_, 1, v___x_2652_);
lean_ctor_set(v___x_2655_, 2, v___x_2654_);
v_toCold_2656_ = lean_ctor_get(v_a_2542_, 0);
v_cancelTk_x3f_2657_ = lean_ctor_get(v_toCold_2656_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2657_) == 1)
{
lean_object* v_val_2658_; uint8_t v___x_2659_; 
v_val_2658_ = lean_ctor_get(v_cancelTk_x3f_2657_, 0);
v___x_2659_ = l_IO_CancelToken_isSet(v_val_2658_);
if (v___x_2659_ == 0)
{
lean_dec_ref_known(v___x_2655_, 3);
goto v___jp_2593_;
}
else
{
lean_object* v___x_4224__overap_2660_; lean_object* v___x_2661_; 
v___x_4224__overap_2660_ = l_Lean_throwInterruptException___redArg(v___x_2655_);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
v___x_2661_ = lean_apply_3(v___x_4224__overap_2660_, v_a_2542_, v_a_2543_, lean_box(0));
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_dec_ref_known(v___x_2661_, 1);
goto v___jp_2593_;
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_a_2589_);
lean_dec_ref(v_inferType_2539_);
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2655_, 3);
goto v___jp_2593_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v_inferType_2539_);
v_a_2717_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2588_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2588_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_dec_ref(v_e_2538_);
goto v___jp_2545_;
}
}
v___jp_2545_:
{
lean_object* v___x_2546_; lean_object* v_toApplicative_2547_; lean_object* v_toFunctor_2548_; lean_object* v_toSeq_2549_; lean_object* v_toSeqLeft_2550_; lean_object* v_toSeqRight_2551_; lean_object* v___f_2552_; lean_object* v___f_2553_; lean_object* v___f_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___f_2558_; lean_object* v___f_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v_toCold_2567_; lean_object* v_cancelTk_x3f_2568_; 
v___x_2546_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2547_ = lean_ctor_get(v___x_2546_, 0);
v_toFunctor_2548_ = lean_ctor_get(v_toApplicative_2547_, 0);
v_toSeq_2549_ = lean_ctor_get(v_toApplicative_2547_, 2);
v_toSeqLeft_2550_ = lean_ctor_get(v_toApplicative_2547_, 3);
v_toSeqRight_2551_ = lean_ctor_get(v_toApplicative_2547_, 4);
v___f_2552_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2553_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2548_, 2);
v___f_2554_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2554_, 0, v_toFunctor_2548_);
v___f_2555_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2555_, 0, v_toFunctor_2548_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___f_2554_);
lean_ctor_set(v___x_2556_, 1, v___f_2555_);
lean_inc(v_toSeqRight_2551_);
v___f_2557_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2557_, 0, v_toSeqRight_2551_);
lean_inc(v_toSeqLeft_2550_);
v___f_2558_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2558_, 0, v_toSeqLeft_2550_);
lean_inc(v_toSeq_2549_);
v___f_2559_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2559_, 0, v_toSeq_2549_);
v___x_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2556_);
lean_ctor_set(v___x_2560_, 1, v___f_2552_);
lean_ctor_set(v___x_2560_, 2, v___f_2559_);
lean_ctor_set(v___x_2560_, 3, v___f_2558_);
lean_ctor_set(v___x_2560_, 4, v___f_2557_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v___f_2553_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2563_ = l_Lean_Core_instMonadRefCoreM;
v___x_2564_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2565_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2564_, v___x_2561_);
v___x_2566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2562_);
lean_ctor_set(v___x_2566_, 1, v___x_2563_);
lean_ctor_set(v___x_2566_, 2, v___x_2565_);
v_toCold_2567_ = lean_ctor_get(v_a_2542_, 0);
v_cancelTk_x3f_2568_ = lean_ctor_get(v_toCold_2567_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2568_) == 1)
{
lean_object* v_val_2569_; uint8_t v___x_2570_; 
v_val_2569_ = lean_ctor_get(v_cancelTk_x3f_2568_, 0);
v___x_2570_ = l_IO_CancelToken_isSet(v_val_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref_known(v___x_2566_, 3);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
lean_inc(v_a_2541_);
lean_inc_ref(v_a_2540_);
v___x_2571_ = lean_apply_5(v_inferType_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, lean_box(0));
return v___x_2571_;
}
else
{
lean_object* v___x_4199__overap_2572_; lean_object* v___x_2573_; 
v___x_4199__overap_2572_ = l_Lean_throwInterruptException___redArg(v___x_2566_);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
v___x_2573_ = lean_apply_3(v___x_4199__overap_2572_, v_a_2542_, v_a_2543_, lean_box(0));
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref_known(v___x_2573_, 1);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
lean_inc(v_a_2541_);
lean_inc_ref(v_a_2540_);
v___x_2574_ = lean_apply_5(v_inferType_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, lean_box(0));
return v___x_2574_;
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref(v_inferType_2539_);
v_a_2575_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2573_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2573_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
else
{
lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2566_, 3);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
lean_inc(v_a_2541_);
lean_inc_ref(v_a_2540_);
v___x_2583_ = lean_apply_5(v_inferType_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, lean_box(0));
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2725_, lean_object* v_inferType_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2725_, v_inferType_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2786_; uint8_t v_beta_2787_; 
v___x_2786_ = l_Lean_Meta_Context_config(v___y_2734_);
v_beta_2787_ = lean_ctor_get_uint8(v___x_2786_, 13);
if (v_beta_2787_ == 0)
{
lean_dec_ref(v___x_2786_);
goto v___jp_2739_;
}
else
{
uint8_t v_iota_2788_; 
v_iota_2788_ = lean_ctor_get_uint8(v___x_2786_, 12);
if (v_iota_2788_ == 0)
{
lean_dec_ref(v___x_2786_);
goto v___jp_2739_;
}
else
{
uint8_t v_zeta_2789_; 
v_zeta_2789_ = lean_ctor_get_uint8(v___x_2786_, 15);
if (v_zeta_2789_ == 0)
{
lean_dec_ref(v___x_2786_);
goto v___jp_2739_;
}
else
{
uint8_t v_zetaHave_2790_; 
v_zetaHave_2790_ = lean_ctor_get_uint8(v___x_2786_, 18);
if (v_zetaHave_2790_ == 0)
{
lean_dec_ref(v___x_2786_);
goto v___jp_2739_;
}
else
{
uint8_t v_zetaDelta_2791_; 
v_zetaDelta_2791_ = lean_ctor_get_uint8(v___x_2786_, 16);
if (v_zetaDelta_2791_ == 0)
{
lean_dec_ref(v___x_2786_);
goto v___jp_2739_;
}
else
{
uint8_t v_etaStruct_2792_; uint8_t v_proj_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_etaStruct_2792_ = lean_ctor_get_uint8(v___x_2786_, 10);
v_proj_2793_ = lean_ctor_get_uint8(v___x_2786_, 14);
lean_dec_ref(v___x_2786_);
v___x_2794_ = lean_box(v_proj_2793_);
v___x_2795_ = lean_obj_tag_nat(v___x_2794_);
lean_dec(v___x_2794_);
v___x_2796_ = lean_unsigned_to_nat(2u);
v___x_2797_ = lean_nat_dec_eq(v___x_2795_, v___x_2796_);
if (v___x_2797_ == 0)
{
goto v___jp_2739_;
}
else
{
uint8_t v___x_2798_; uint8_t v___x_2799_; 
v___x_2798_ = 0;
v___x_2799_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2792_, v___x_2798_);
if (v___x_2799_ == 0)
{
goto v___jp_2739_;
}
else
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_apply_5(v_x_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, lean_box(0));
return v___x_2800_;
}
}
}
}
}
}
}
v___jp_2739_:
{
lean_object* v___x_2740_; uint8_t v_foApprox_2741_; uint8_t v_ctxApprox_2742_; uint8_t v_quasiPatternApprox_2743_; uint8_t v_constApprox_2744_; uint8_t v_isDefEqStuckEx_2745_; uint8_t v_unificationHints_2746_; uint8_t v_proofIrrelevance_2747_; uint8_t v_assignSyntheticOpaque_2748_; uint8_t v_offsetCnstrs_2749_; uint8_t v_transparency_2750_; uint8_t v_univApprox_2751_; uint8_t v_zetaUnused_2752_; uint8_t v_canUnfoldPredicateConfig_2753_; uint8_t v_stringLitToCtor_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2785_; 
v___x_2740_ = l_Lean_Meta_Context_config(v___y_2734_);
v_foApprox_2741_ = lean_ctor_get_uint8(v___x_2740_, 0);
v_ctxApprox_2742_ = lean_ctor_get_uint8(v___x_2740_, 1);
v_quasiPatternApprox_2743_ = lean_ctor_get_uint8(v___x_2740_, 2);
v_constApprox_2744_ = lean_ctor_get_uint8(v___x_2740_, 3);
v_isDefEqStuckEx_2745_ = lean_ctor_get_uint8(v___x_2740_, 4);
v_unificationHints_2746_ = lean_ctor_get_uint8(v___x_2740_, 5);
v_proofIrrelevance_2747_ = lean_ctor_get_uint8(v___x_2740_, 6);
v_assignSyntheticOpaque_2748_ = lean_ctor_get_uint8(v___x_2740_, 7);
v_offsetCnstrs_2749_ = lean_ctor_get_uint8(v___x_2740_, 8);
v_transparency_2750_ = lean_ctor_get_uint8(v___x_2740_, 9);
v_univApprox_2751_ = lean_ctor_get_uint8(v___x_2740_, 11);
v_zetaUnused_2752_ = lean_ctor_get_uint8(v___x_2740_, 17);
v_canUnfoldPredicateConfig_2753_ = lean_ctor_get_uint8(v___x_2740_, 19);
v_stringLitToCtor_2754_ = lean_ctor_get_uint8(v___x_2740_, 20);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2756_ = v___x_2740_;
v_isShared_2757_ = v_isSharedCheck_2785_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v___x_2740_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2785_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
uint8_t v___x_2758_; uint8_t v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2762_; 
v___x_2758_ = 1;
v___x_2759_ = 0;
v___x_2760_ = 2;
if (v_isShared_2757_ == 0)
{
v___x_2762_ = v___x_2756_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 0, v_foApprox_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 1, v_ctxApprox_2742_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 2, v_quasiPatternApprox_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 3, v_constApprox_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 4, v_isDefEqStuckEx_2745_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 5, v_unificationHints_2746_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 6, v_proofIrrelevance_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 7, v_assignSyntheticOpaque_2748_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 8, v_offsetCnstrs_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 9, v_transparency_2750_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 11, v_univApprox_2751_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 17, v_zetaUnused_2752_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 19, v_canUnfoldPredicateConfig_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2784_, 20, v_stringLitToCtor_2754_);
v___x_2762_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
uint8_t v_trackZetaDelta_2763_; lean_object* v_zetaDeltaSet_2764_; lean_object* v_lctx_2765_; lean_object* v_localInstances_2766_; lean_object* v_defEqCtx_x3f_2767_; lean_object* v_synthPendingDepth_2768_; lean_object* v_customCanUnfoldPredicate_x3f_2769_; uint8_t v_univApprox_2770_; uint8_t v_inTypeClassResolution_2771_; uint8_t v_cacheInferType_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2782_; 
lean_ctor_set_uint8(v___x_2762_, 10, v___x_2759_);
lean_ctor_set_uint8(v___x_2762_, 12, v___x_2758_);
lean_ctor_set_uint8(v___x_2762_, 13, v___x_2758_);
lean_ctor_set_uint8(v___x_2762_, 14, v___x_2760_);
lean_ctor_set_uint8(v___x_2762_, 15, v___x_2758_);
lean_ctor_set_uint8(v___x_2762_, 16, v___x_2758_);
lean_ctor_set_uint8(v___x_2762_, 18, v___x_2758_);
v_trackZetaDelta_2763_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7);
v_zetaDeltaSet_2764_ = lean_ctor_get(v___y_2734_, 1);
v_lctx_2765_ = lean_ctor_get(v___y_2734_, 2);
v_localInstances_2766_ = lean_ctor_get(v___y_2734_, 3);
v_defEqCtx_x3f_2767_ = lean_ctor_get(v___y_2734_, 4);
v_synthPendingDepth_2768_ = lean_ctor_get(v___y_2734_, 5);
v_customCanUnfoldPredicate_x3f_2769_ = lean_ctor_get(v___y_2734_, 6);
v_univApprox_2770_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2771_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7 + 2);
v_cacheInferType_2772_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*7 + 3);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___y_2734_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; 
v_unused_2783_ = lean_ctor_get(v___y_2734_, 0);
lean_dec(v_unused_2783_);
v___x_2774_ = v___y_2734_;
v_isShared_2775_ = v_isSharedCheck_2782_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2769_);
lean_inc(v_synthPendingDepth_2768_);
lean_inc(v_defEqCtx_x3f_2767_);
lean_inc(v_localInstances_2766_);
lean_inc(v_lctx_2765_);
lean_inc(v_zetaDeltaSet_2764_);
lean_dec(v___y_2734_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2782_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint64_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2776_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2762_);
v___x_2777_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2777_, 0, v___x_2762_);
lean_ctor_set_uint64(v___x_2777_, sizeof(void*)*1, v___x_2776_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2777_);
v___x_2779_ = v___x_2774_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_zetaDeltaSet_2764_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_lctx_2765_);
lean_ctor_set(v_reuseFailAlloc_2781_, 3, v_localInstances_2766_);
lean_ctor_set(v_reuseFailAlloc_2781_, 4, v_defEqCtx_x3f_2767_);
lean_ctor_set(v_reuseFailAlloc_2781_, 5, v_synthPendingDepth_2768_);
lean_ctor_set(v_reuseFailAlloc_2781_, 6, v_customCanUnfoldPredicate_x3f_2769_);
lean_ctor_set_uint8(v_reuseFailAlloc_2781_, sizeof(void*)*7, v_trackZetaDelta_2763_);
lean_ctor_set_uint8(v_reuseFailAlloc_2781_, sizeof(void*)*7 + 1, v_univApprox_2770_);
lean_ctor_set_uint8(v_reuseFailAlloc_2781_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2781_, sizeof(void*)*7 + 3, v_cacheInferType_2772_);
v___x_2779_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_apply_5(v_x_2733_, v___x_2779_, v___y_2735_, v___y_2736_, v___y_2737_, lean_box(0));
return v___x_2780_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___y_2815_; lean_object* v___x_2832_; uint8_t v_transparency_2833_; uint8_t v___x_2834_; uint8_t v___x_2835_; 
v___x_2832_ = l_Lean_Meta_Context_config(v_a_2809_);
v_transparency_2833_ = lean_ctor_get_uint8(v___x_2832_, 9);
lean_dec_ref(v___x_2832_);
v___x_2834_ = 1;
v___x_2835_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2833_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; 
lean_inc(v_a_2812_);
lean_inc_ref(v_a_2811_);
lean_inc(v_a_2810_);
lean_inc_ref(v_a_2809_);
v___x_2836_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
v___y_2815_ = v___x_2836_;
goto v___jp_2814_;
}
else
{
lean_object* v_keyedConfig_2837_; uint8_t v_trackZetaDelta_2838_; lean_object* v_zetaDeltaSet_2839_; lean_object* v_lctx_2840_; lean_object* v_localInstances_2841_; lean_object* v_defEqCtx_x3f_2842_; lean_object* v_synthPendingDepth_2843_; lean_object* v_customCanUnfoldPredicate_x3f_2844_; uint8_t v_univApprox_2845_; uint8_t v_inTypeClassResolution_2846_; uint8_t v_cacheInferType_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_keyedConfig_2837_ = lean_ctor_get(v_a_2809_, 0);
v_trackZetaDelta_2838_ = lean_ctor_get_uint8(v_a_2809_, sizeof(void*)*7);
v_zetaDeltaSet_2839_ = lean_ctor_get(v_a_2809_, 1);
v_lctx_2840_ = lean_ctor_get(v_a_2809_, 2);
v_localInstances_2841_ = lean_ctor_get(v_a_2809_, 3);
v_defEqCtx_x3f_2842_ = lean_ctor_get(v_a_2809_, 4);
v_synthPendingDepth_2843_ = lean_ctor_get(v_a_2809_, 5);
v_customCanUnfoldPredicate_x3f_2844_ = lean_ctor_get(v_a_2809_, 6);
v_univApprox_2845_ = lean_ctor_get_uint8(v_a_2809_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2846_ = lean_ctor_get_uint8(v_a_2809_, sizeof(void*)*7 + 2);
v_cacheInferType_2847_ = lean_ctor_get_uint8(v_a_2809_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2837_);
v___x_2848_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2834_, v_keyedConfig_2837_);
lean_inc(v_customCanUnfoldPredicate_x3f_2844_);
lean_inc(v_synthPendingDepth_2843_);
lean_inc(v_defEqCtx_x3f_2842_);
lean_inc_ref(v_localInstances_2841_);
lean_inc_ref(v_lctx_2840_);
lean_inc(v_zetaDeltaSet_2839_);
v___x_2849_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v_zetaDeltaSet_2839_);
lean_ctor_set(v___x_2849_, 2, v_lctx_2840_);
lean_ctor_set(v___x_2849_, 3, v_localInstances_2841_);
lean_ctor_set(v___x_2849_, 4, v_defEqCtx_x3f_2842_);
lean_ctor_set(v___x_2849_, 5, v_synthPendingDepth_2843_);
lean_ctor_set(v___x_2849_, 6, v_customCanUnfoldPredicate_x3f_2844_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7, v_trackZetaDelta_2838_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7 + 1, v_univApprox_2845_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2846_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7 + 3, v_cacheInferType_2847_);
lean_inc(v_a_2812_);
lean_inc_ref(v_a_2811_);
lean_inc(v_a_2810_);
v___x_2850_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2808_, v___x_2849_, v_a_2810_, v_a_2811_, v_a_2812_);
v___y_2815_ = v___x_2850_;
goto v___jp_2814_;
}
v___jp_2814_:
{
if (lean_obj_tag(v___y_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___y_2815_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___y_2815_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___y_2815_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___y_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
v_a_2824_ = lean_ctor_get(v___y_2815_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___y_2815_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___y_2815_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___y_2815_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2858_, lean_object* v_x_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v___y_2866_; lean_object* v___x_2883_; uint8_t v_transparency_2884_; uint8_t v___x_2885_; uint8_t v___x_2886_; 
v___x_2883_ = l_Lean_Meta_Context_config(v_a_2860_);
v_transparency_2884_ = lean_ctor_get_uint8(v___x_2883_, 9);
lean_dec_ref(v___x_2883_);
v___x_2885_ = 1;
v___x_2886_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2884_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_inc(v_a_2863_);
lean_inc_ref(v_a_2862_);
lean_inc(v_a_2861_);
lean_inc_ref(v_a_2860_);
v___x_2887_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
v___y_2866_ = v___x_2887_;
goto v___jp_2865_;
}
else
{
lean_object* v_keyedConfig_2888_; uint8_t v_trackZetaDelta_2889_; lean_object* v_zetaDeltaSet_2890_; lean_object* v_lctx_2891_; lean_object* v_localInstances_2892_; lean_object* v_defEqCtx_x3f_2893_; lean_object* v_synthPendingDepth_2894_; lean_object* v_customCanUnfoldPredicate_x3f_2895_; uint8_t v_univApprox_2896_; uint8_t v_inTypeClassResolution_2897_; uint8_t v_cacheInferType_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_keyedConfig_2888_ = lean_ctor_get(v_a_2860_, 0);
v_trackZetaDelta_2889_ = lean_ctor_get_uint8(v_a_2860_, sizeof(void*)*7);
v_zetaDeltaSet_2890_ = lean_ctor_get(v_a_2860_, 1);
v_lctx_2891_ = lean_ctor_get(v_a_2860_, 2);
v_localInstances_2892_ = lean_ctor_get(v_a_2860_, 3);
v_defEqCtx_x3f_2893_ = lean_ctor_get(v_a_2860_, 4);
v_synthPendingDepth_2894_ = lean_ctor_get(v_a_2860_, 5);
v_customCanUnfoldPredicate_x3f_2895_ = lean_ctor_get(v_a_2860_, 6);
v_univApprox_2896_ = lean_ctor_get_uint8(v_a_2860_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2897_ = lean_ctor_get_uint8(v_a_2860_, sizeof(void*)*7 + 2);
v_cacheInferType_2898_ = lean_ctor_get_uint8(v_a_2860_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2888_);
v___x_2899_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2885_, v_keyedConfig_2888_);
lean_inc(v_customCanUnfoldPredicate_x3f_2895_);
lean_inc(v_synthPendingDepth_2894_);
lean_inc(v_defEqCtx_x3f_2893_);
lean_inc_ref(v_localInstances_2892_);
lean_inc_ref(v_lctx_2891_);
lean_inc(v_zetaDeltaSet_2890_);
v___x_2900_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v_zetaDeltaSet_2890_);
lean_ctor_set(v___x_2900_, 2, v_lctx_2891_);
lean_ctor_set(v___x_2900_, 3, v_localInstances_2892_);
lean_ctor_set(v___x_2900_, 4, v_defEqCtx_x3f_2893_);
lean_ctor_set(v___x_2900_, 5, v_synthPendingDepth_2894_);
lean_ctor_set(v___x_2900_, 6, v_customCanUnfoldPredicate_x3f_2895_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*7, v_trackZetaDelta_2889_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*7 + 1, v_univApprox_2896_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2897_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*7 + 3, v_cacheInferType_2898_);
lean_inc(v_a_2863_);
lean_inc_ref(v_a_2862_);
lean_inc(v_a_2861_);
v___x_2901_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2859_, v___x_2900_, v_a_2861_, v_a_2862_, v_a_2863_);
v___y_2866_ = v___x_2901_;
goto v___jp_2865_;
}
v___jp_2865_:
{
if (lean_obj_tag(v___y_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_a_2867_ = lean_ctor_get(v___y_2866_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___y_2866_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___y_2866_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___y_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_a_2875_ = lean_ctor_get(v___y_2866_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___y_2866_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___y_2866_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___y_2866_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2902_, lean_object* v_x_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2902_, v_x_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
return v_res_2909_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = lean_box(0);
v___x_2911_ = l_Lean_interruptExceptionId;
v___x_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___x_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
lean_object* v_ks_2932_; lean_object* v_vs_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2965_; 
v_ks_2932_ = lean_ctor_get(v_x_2928_, 0);
v_vs_2933_ = lean_ctor_get(v_x_2928_, 1);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_x_2928_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2935_ = v_x_2928_;
v_isShared_2936_ = v_isSharedCheck_2965_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_vs_2933_);
lean_inc(v_ks_2932_);
lean_dec(v_x_2928_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2965_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = lean_array_get_size(v_ks_2932_);
v___x_2938_ = lean_nat_dec_lt(v_x_2929_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec(v_x_2929_);
v___x_2939_ = lean_array_push(v_ks_2932_, v_x_2930_);
v___x_2940_ = lean_array_push(v_vs_2933_, v_x_2931_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2940_);
lean_ctor_set(v___x_2935_, 0, v___x_2939_);
v___x_2942_ = v___x_2935_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
else
{
lean_object* v_expr_2944_; uint64_t v_configKey_2945_; lean_object* v_k_x27_2946_; lean_object* v_expr_2947_; uint64_t v_configKey_2948_; uint64_t v___x_2949_; uint64_t v___x_2950_; uint64_t v___x_2951_; uint64_t v___x_2952_; uint8_t v___x_2953_; 
v_expr_2944_ = lean_ctor_get(v_x_2930_, 0);
v_configKey_2945_ = lean_ctor_get_uint64(v_x_2930_, sizeof(void*)*1);
v_k_x27_2946_ = lean_array_fget_borrowed(v_ks_2932_, v_x_2929_);
v_expr_2947_ = lean_ctor_get(v_k_x27_2946_, 0);
v_configKey_2948_ = lean_ctor_get_uint64(v_k_x27_2946_, sizeof(void*)*1);
v___x_2949_ = l_Lean_Expr_hash(v_expr_2944_);
v___x_2950_ = lean_uint64_mix_hash(v___x_2949_, v_configKey_2945_);
v___x_2951_ = l_Lean_Expr_hash(v_expr_2947_);
v___x_2952_ = lean_uint64_mix_hash(v___x_2951_, v_configKey_2948_);
v___x_2953_ = lean_uint64_dec_eq(v___x_2950_, v___x_2952_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2955_; 
if (v_isShared_2936_ == 0)
{
v___x_2955_ = v___x_2935_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_ks_2932_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_vs_2933_);
v___x_2955_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = lean_nat_add(v_x_2929_, v___x_2956_);
lean_dec(v_x_2929_);
v_x_2928_ = v___x_2955_;
v_x_2929_ = v___x_2957_;
goto _start;
}
}
else
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2960_ = lean_array_fset(v_ks_2932_, v_x_2929_, v_x_2930_);
v___x_2961_ = lean_array_fset(v_vs_2933_, v_x_2929_, v_x_2931_);
lean_dec(v_x_2929_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v___x_2961_);
lean_ctor_set(v___x_2935_, 0, v___x_2960_);
v___x_2963_ = v___x_2935_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2966_, lean_object* v_k_2967_, lean_object* v_v_2968_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_n_2966_, v___x_2969_, v_k_2967_, v_v_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2971_, size_t v_x_2972_, size_t v_x_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_){
_start:
{
if (lean_obj_tag(v_x_2971_) == 0)
{
lean_object* v_es_2976_; size_t v___x_2977_; size_t v___x_2978_; lean_object* v_j_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_es_2976_ = lean_ctor_get(v_x_2971_, 0);
v___x_2977_ = ((size_t)31ULL);
v___x_2978_ = lean_usize_land(v_x_2972_, v___x_2977_);
v_j_2979_ = lean_usize_to_nat(v___x_2978_);
v___x_2980_ = lean_array_get_size(v_es_2976_);
v___x_2981_ = lean_nat_dec_lt(v_j_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec(v_j_2979_);
lean_dec(v_x_2975_);
lean_dec_ref(v_x_2974_);
return v_x_2971_;
}
else
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3028_; 
lean_inc_ref(v_es_2976_);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_x_2971_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; 
v_unused_3029_ = lean_ctor_get(v_x_2971_, 0);
lean_dec(v_unused_3029_);
v___x_2983_ = v_x_2971_;
v_isShared_2984_ = v_isSharedCheck_3028_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v_x_2971_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3028_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_v_2985_; lean_object* v___x_2986_; lean_object* v_xs_x27_2987_; lean_object* v___y_2989_; 
v_v_2985_ = lean_array_fget(v_es_2976_, v_j_2979_);
v___x_2986_ = lean_box(0);
v_xs_x27_2987_ = lean_array_fset(v_es_2976_, v_j_2979_, v___x_2986_);
switch(lean_obj_tag(v_v_2985_))
{
case 0:
{
lean_object* v_key_2994_; lean_object* v_val_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3013_; 
v_key_2994_ = lean_ctor_get(v_v_2985_, 0);
v_val_2995_ = lean_ctor_get(v_v_2985_, 1);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_v_2985_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2997_ = v_v_2985_;
v_isShared_2998_ = v_isSharedCheck_3013_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_val_2995_);
lean_inc(v_key_2994_);
lean_dec(v_v_2985_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3013_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v_expr_2999_; uint64_t v_configKey_3000_; lean_object* v_expr_3001_; uint64_t v_configKey_3002_; uint64_t v___x_3003_; uint64_t v___x_3004_; uint64_t v___x_3005_; uint64_t v___x_3006_; uint8_t v___x_3007_; 
v_expr_2999_ = lean_ctor_get(v_x_2974_, 0);
v_configKey_3000_ = lean_ctor_get_uint64(v_x_2974_, sizeof(void*)*1);
v_expr_3001_ = lean_ctor_get(v_key_2994_, 0);
v_configKey_3002_ = lean_ctor_get_uint64(v_key_2994_, sizeof(void*)*1);
v___x_3003_ = l_Lean_Expr_hash(v_expr_2999_);
v___x_3004_ = lean_uint64_mix_hash(v___x_3003_, v_configKey_3000_);
v___x_3005_ = l_Lean_Expr_hash(v_expr_3001_);
v___x_3006_ = lean_uint64_mix_hash(v___x_3005_, v_configKey_3002_);
v___x_3007_ = lean_uint64_dec_eq(v___x_3004_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_del_object(v___x_2997_);
v___x_3008_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2994_, v_val_2995_, v_x_2974_, v_x_2975_);
v___x_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
v___y_2989_ = v___x_3009_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3011_; 
lean_dec(v_val_2995_);
lean_dec(v_key_2994_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 1, v_x_2975_);
lean_ctor_set(v___x_2997_, 0, v_x_2974_);
v___x_3011_ = v___x_2997_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_x_2974_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_x_2975_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
v___y_2989_ = v___x_3011_;
goto v___jp_2988_;
}
}
}
}
case 1:
{
lean_object* v_node_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3026_; 
v_node_3014_ = lean_ctor_get(v_v_2985_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_v_2985_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3016_ = v_v_2985_;
v_isShared_3017_ = v_isSharedCheck_3026_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_node_3014_);
lean_dec(v_v_2985_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3026_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
size_t v___x_3018_; size_t v___x_3019_; size_t v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3018_ = ((size_t)5ULL);
v___x_3019_ = lean_usize_shift_right(v_x_2972_, v___x_3018_);
v___x_3020_ = ((size_t)1ULL);
v___x_3021_ = lean_usize_add(v_x_2973_, v___x_3020_);
v___x_3022_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_3014_, v___x_3019_, v___x_3021_, v_x_2974_, v_x_2975_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3022_);
v___x_3024_ = v___x_3016_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
v___y_2989_ = v___x_3024_;
goto v___jp_2988_;
}
}
}
default: 
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_x_2974_);
lean_ctor_set(v___x_3027_, 1, v_x_2975_);
v___y_2989_ = v___x_3027_;
goto v___jp_2988_;
}
}
v___jp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2990_ = lean_array_fset(v_xs_x27_2987_, v_j_2979_, v___y_2989_);
lean_dec(v_j_2979_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2990_);
v___x_2992_ = v___x_2983_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
else
{
lean_object* v_ks_3030_; lean_object* v_vs_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3049_; 
v_ks_3030_ = lean_ctor_get(v_x_2971_, 0);
v_vs_3031_ = lean_ctor_get(v_x_2971_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_x_2971_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3033_ = v_x_2971_;
v_isShared_3034_ = v_isSharedCheck_3049_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_vs_3031_);
lean_inc(v_ks_3030_);
lean_dec(v_x_2971_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3049_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_ks_3030_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_vs_3031_);
v___x_3036_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v_newNode_3037_; size_t v___x_3038_; uint8_t v___x_3039_; 
v_newNode_3037_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_3036_, v_x_2974_, v_x_2975_);
v___x_3038_ = ((size_t)7ULL);
v___x_3039_ = lean_usize_dec_le(v___x_3038_, v_x_2973_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3040_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3037_);
v___x_3041_ = lean_unsigned_to_nat(4u);
v___x_3042_ = lean_nat_dec_lt(v___x_3040_, v___x_3041_);
lean_dec(v___x_3040_);
if (v___x_3042_ == 0)
{
lean_object* v_ks_3043_; lean_object* v_vs_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_ks_3043_ = lean_ctor_get(v_newNode_3037_, 0);
lean_inc_ref(v_ks_3043_);
v_vs_3044_ = lean_ctor_get(v_newNode_3037_, 1);
lean_inc_ref(v_vs_3044_);
lean_dec_ref(v_newNode_3037_);
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3047_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2973_, v_ks_3043_, v_vs_3044_, v___x_3045_, v___x_3046_);
lean_dec_ref(v_vs_3044_);
lean_dec_ref(v_ks_3043_);
return v___x_3047_;
}
else
{
return v_newNode_3037_;
}
}
else
{
return v_newNode_3037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3050_, lean_object* v_keys_3051_, lean_object* v_vals_3052_, lean_object* v_i_3053_, lean_object* v_entries_3054_){
_start:
{
lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3055_ = lean_array_get_size(v_keys_3051_);
v___x_3056_ = lean_nat_dec_lt(v_i_3053_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_dec(v_i_3053_);
return v_entries_3054_;
}
else
{
lean_object* v_k_3057_; lean_object* v_expr_3058_; uint64_t v_configKey_3059_; lean_object* v_v_3060_; uint64_t v___x_3061_; uint64_t v___x_3062_; size_t v_h_3063_; size_t v___x_3064_; lean_object* v___x_3065_; size_t v___x_3066_; size_t v___x_3067_; size_t v___x_3068_; size_t v_h_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_k_3057_ = lean_array_fget_borrowed(v_keys_3051_, v_i_3053_);
v_expr_3058_ = lean_ctor_get(v_k_3057_, 0);
v_configKey_3059_ = lean_ctor_get_uint64(v_k_3057_, sizeof(void*)*1);
v_v_3060_ = lean_array_fget_borrowed(v_vals_3052_, v_i_3053_);
v___x_3061_ = l_Lean_Expr_hash(v_expr_3058_);
v___x_3062_ = lean_uint64_mix_hash(v___x_3061_, v_configKey_3059_);
v_h_3063_ = lean_uint64_to_usize(v___x_3062_);
v___x_3064_ = ((size_t)5ULL);
v___x_3065_ = lean_unsigned_to_nat(1u);
v___x_3066_ = ((size_t)1ULL);
v___x_3067_ = lean_usize_sub(v_depth_3050_, v___x_3066_);
v___x_3068_ = lean_usize_mul(v___x_3064_, v___x_3067_);
v_h_3069_ = lean_usize_shift_right(v_h_3063_, v___x_3068_);
v___x_3070_ = lean_nat_add(v_i_3053_, v___x_3065_);
lean_dec(v_i_3053_);
lean_inc(v_v_3060_);
lean_inc(v_k_3057_);
v___x_3071_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3054_, v_h_3069_, v_depth_3050_, v_k_3057_, v_v_3060_);
v_i_3053_ = v___x_3070_;
v_entries_3054_ = v___x_3071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3073_, lean_object* v_keys_3074_, lean_object* v_vals_3075_, lean_object* v_i_3076_, lean_object* v_entries_3077_){
_start:
{
size_t v_depth_boxed_3078_; lean_object* v_res_3079_; 
v_depth_boxed_3078_ = lean_unbox_usize(v_depth_3073_);
lean_dec(v_depth_3073_);
v_res_3079_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3078_, v_keys_3074_, v_vals_3075_, v_i_3076_, v_entries_3077_);
lean_dec_ref(v_vals_3075_);
lean_dec_ref(v_keys_3074_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
size_t v_x_3752__boxed_3085_; size_t v_x_3753__boxed_3086_; lean_object* v_res_3087_; 
v_x_3752__boxed_3085_ = lean_unbox_usize(v_x_3081_);
lean_dec(v_x_3081_);
v_x_3753__boxed_3086_ = lean_unbox_usize(v_x_3082_);
lean_dec(v_x_3082_);
v_res_3087_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3080_, v_x_3752__boxed_3085_, v_x_3753__boxed_3086_, v_x_3083_, v_x_3084_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3088_, lean_object* v_x_3089_, lean_object* v_x_3090_){
_start:
{
lean_object* v_expr_3091_; uint64_t v_configKey_3092_; uint64_t v___x_3093_; uint64_t v___x_3094_; size_t v___x_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v_expr_3091_ = lean_ctor_get(v_x_3089_, 0);
v_configKey_3092_ = lean_ctor_get_uint64(v_x_3089_, sizeof(void*)*1);
v___x_3093_ = l_Lean_Expr_hash(v_expr_3091_);
v___x_3094_ = lean_uint64_mix_hash(v___x_3093_, v_configKey_3092_);
v___x_3095_ = lean_uint64_to_usize(v___x_3094_);
v___x_3096_ = ((size_t)1ULL);
v___x_3097_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3088_, v___x_3095_, v___x_3096_, v_x_3089_, v_x_3090_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3098_, lean_object* v_vals_3099_, lean_object* v_i_3100_, lean_object* v_k_3101_){
_start:
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = lean_array_get_size(v_keys_3098_);
v___x_3103_ = lean_nat_dec_lt(v_i_3100_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
lean_dec(v_i_3100_);
v___x_3104_ = lean_box(0);
return v___x_3104_;
}
else
{
lean_object* v_expr_3105_; uint64_t v_configKey_3106_; lean_object* v_k_x27_3107_; lean_object* v_expr_3108_; uint64_t v_configKey_3109_; uint64_t v___x_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v___x_3113_; uint8_t v___x_3114_; 
v_expr_3105_ = lean_ctor_get(v_k_3101_, 0);
v_configKey_3106_ = lean_ctor_get_uint64(v_k_3101_, sizeof(void*)*1);
v_k_x27_3107_ = lean_array_fget_borrowed(v_keys_3098_, v_i_3100_);
v_expr_3108_ = lean_ctor_get(v_k_x27_3107_, 0);
v_configKey_3109_ = lean_ctor_get_uint64(v_k_x27_3107_, sizeof(void*)*1);
v___x_3110_ = l_Lean_Expr_hash(v_expr_3105_);
v___x_3111_ = lean_uint64_mix_hash(v___x_3110_, v_configKey_3106_);
v___x_3112_ = l_Lean_Expr_hash(v_expr_3108_);
v___x_3113_ = lean_uint64_mix_hash(v___x_3112_, v_configKey_3109_);
v___x_3114_ = lean_uint64_dec_eq(v___x_3111_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_add(v_i_3100_, v___x_3115_);
lean_dec(v_i_3100_);
v_i_3100_ = v___x_3116_;
goto _start;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_array_fget_borrowed(v_vals_3099_, v_i_3100_);
lean_dec(v_i_3100_);
lean_inc(v___x_3118_);
lean_inc(v_k_x27_3107_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_k_x27_3107_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3121_, lean_object* v_vals_3122_, lean_object* v_i_3123_, lean_object* v_k_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3121_, v_vals_3122_, v_i_3123_, v_k_3124_);
lean_dec_ref(v_k_3124_);
lean_dec_ref(v_vals_3122_);
lean_dec_ref(v_keys_3121_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3126_, size_t v_x_3127_, lean_object* v_x_3128_){
_start:
{
if (lean_obj_tag(v_x_3126_) == 0)
{
lean_object* v_es_3129_; lean_object* v___x_3130_; size_t v___x_3131_; size_t v___x_3132_; lean_object* v_j_3133_; lean_object* v___x_3134_; 
v_es_3129_ = lean_ctor_get(v_x_3126_, 0);
v___x_3130_ = lean_box(2);
v___x_3131_ = ((size_t)31ULL);
v___x_3132_ = lean_usize_land(v_x_3127_, v___x_3131_);
v_j_3133_ = lean_usize_to_nat(v___x_3132_);
v___x_3134_ = lean_array_get_borrowed(v___x_3130_, v_es_3129_, v_j_3133_);
lean_dec(v_j_3133_);
switch(lean_obj_tag(v___x_3134_))
{
case 0:
{
lean_object* v_key_3135_; lean_object* v_val_3136_; lean_object* v_expr_3137_; uint64_t v_configKey_3138_; lean_object* v_expr_3139_; uint64_t v_configKey_3140_; uint64_t v___x_3141_; uint64_t v___x_3142_; uint64_t v___x_3143_; uint64_t v___x_3144_; uint8_t v___x_3145_; 
v_key_3135_ = lean_ctor_get(v___x_3134_, 0);
v_val_3136_ = lean_ctor_get(v___x_3134_, 1);
v_expr_3137_ = lean_ctor_get(v_x_3128_, 0);
v_configKey_3138_ = lean_ctor_get_uint64(v_x_3128_, sizeof(void*)*1);
v_expr_3139_ = lean_ctor_get(v_key_3135_, 0);
v_configKey_3140_ = lean_ctor_get_uint64(v_key_3135_, sizeof(void*)*1);
v___x_3141_ = l_Lean_Expr_hash(v_expr_3137_);
v___x_3142_ = lean_uint64_mix_hash(v___x_3141_, v_configKey_3138_);
v___x_3143_ = l_Lean_Expr_hash(v_expr_3139_);
v___x_3144_ = lean_uint64_mix_hash(v___x_3143_, v_configKey_3140_);
v___x_3145_ = lean_uint64_dec_eq(v___x_3142_, v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_box(0);
return v___x_3146_;
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_inc(v_val_3136_);
lean_inc(v_key_3135_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_key_3135_);
lean_ctor_set(v___x_3147_, 1, v_val_3136_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
case 1:
{
lean_object* v_node_3149_; size_t v___x_3150_; size_t v___x_3151_; 
v_node_3149_ = lean_ctor_get(v___x_3134_, 0);
v___x_3150_ = ((size_t)5ULL);
v___x_3151_ = lean_usize_shift_right(v_x_3127_, v___x_3150_);
v_x_3126_ = v_node_3149_;
v_x_3127_ = v___x_3151_;
goto _start;
}
default: 
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_box(0);
return v___x_3153_;
}
}
}
else
{
lean_object* v_ks_3154_; lean_object* v_vs_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_ks_3154_ = lean_ctor_get(v_x_3126_, 0);
v_vs_3155_ = lean_ctor_get(v_x_3126_, 1);
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3154_, v_vs_3155_, v___x_3156_, v_x_3128_);
return v___x_3157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3158_, lean_object* v_x_3159_, lean_object* v_x_3160_){
_start:
{
size_t v_x_3978__boxed_3161_; lean_object* v_res_3162_; 
v_x_3978__boxed_3161_ = lean_unbox_usize(v_x_3159_);
lean_dec(v_x_3159_);
v_res_3162_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3158_, v_x_3978__boxed_3161_, v_x_3160_);
lean_dec_ref(v_x_3160_);
lean_dec_ref(v_x_3158_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3163_, lean_object* v_x_3164_){
_start:
{
lean_object* v_expr_3165_; uint64_t v_configKey_3166_; uint64_t v___x_3167_; uint64_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
v_expr_3165_ = lean_ctor_get(v_x_3164_, 0);
v_configKey_3166_ = lean_ctor_get_uint64(v_x_3164_, sizeof(void*)*1);
v___x_3167_ = l_Lean_Expr_hash(v_expr_3165_);
v___x_3168_ = lean_uint64_mix_hash(v___x_3167_, v_configKey_3166_);
v___x_3169_ = lean_uint64_to_usize(v___x_3168_);
v___x_3170_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3163_, v___x_3169_, v_x_3164_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3171_, lean_object* v_x_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3171_, v_x_3172_);
lean_dec_ref(v_x_3172_);
lean_dec_ref(v_x_3171_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(lean_object* v_xs_3174_, lean_object* v_v_3175_, lean_object* v_i_3176_){
_start:
{
lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = lean_array_get_size(v_xs_3174_);
v___x_3178_ = lean_nat_dec_lt(v_i_3176_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_dec(v_i_3176_);
v___x_3179_ = lean_box(0);
return v___x_3179_;
}
else
{
lean_object* v___x_3180_; lean_object* v_expr_3181_; uint64_t v_configKey_3182_; lean_object* v_expr_3183_; uint64_t v_configKey_3184_; uint64_t v___x_3185_; uint64_t v___x_3186_; uint64_t v___x_3187_; uint64_t v___x_3188_; uint8_t v___x_3189_; 
v___x_3180_ = lean_array_fget_borrowed(v_xs_3174_, v_i_3176_);
v_expr_3181_ = lean_ctor_get(v___x_3180_, 0);
v_configKey_3182_ = lean_ctor_get_uint64(v___x_3180_, sizeof(void*)*1);
v_expr_3183_ = lean_ctor_get(v_v_3175_, 0);
v_configKey_3184_ = lean_ctor_get_uint64(v_v_3175_, sizeof(void*)*1);
v___x_3185_ = l_Lean_Expr_hash(v_expr_3181_);
v___x_3186_ = lean_uint64_mix_hash(v___x_3185_, v_configKey_3182_);
v___x_3187_ = l_Lean_Expr_hash(v_expr_3183_);
v___x_3188_ = lean_uint64_mix_hash(v___x_3187_, v_configKey_3184_);
v___x_3189_ = lean_uint64_dec_eq(v___x_3186_, v___x_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_unsigned_to_nat(1u);
v___x_3191_ = lean_nat_add(v_i_3176_, v___x_3190_);
lean_dec(v_i_3176_);
v_i_3176_ = v___x_3191_;
goto _start;
}
else
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_i_3176_);
return v___x_3193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11___boxed(lean_object* v_xs_3194_, lean_object* v_v_3195_, lean_object* v_i_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3194_, v_v_3195_, v_i_3196_);
lean_dec_ref(v_v_3195_);
lean_dec_ref(v_xs_3194_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(lean_object* v_xs_3198_, lean_object* v_v_3199_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_unsigned_to_nat(0u);
v___x_3201_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9_spec__11(v_xs_3198_, v_v_3199_, v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9___boxed(lean_object* v_xs_3202_, lean_object* v_v_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_xs_3202_, v_v_3203_);
lean_dec_ref(v_v_3203_);
lean_dec_ref(v_xs_3202_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(lean_object* v_x_3205_, size_t v_x_3206_, lean_object* v_x_3207_){
_start:
{
if (lean_obj_tag(v_x_3205_) == 0)
{
lean_object* v_es_3208_; lean_object* v___x_3209_; size_t v___x_3210_; size_t v___x_3211_; lean_object* v_j_3212_; lean_object* v_entry_3213_; 
v_es_3208_ = lean_ctor_get(v_x_3205_, 0);
v___x_3209_ = lean_box(2);
v___x_3210_ = ((size_t)31ULL);
v___x_3211_ = lean_usize_land(v_x_3206_, v___x_3210_);
v_j_3212_ = lean_usize_to_nat(v___x_3211_);
v_entry_3213_ = lean_array_get(v___x_3209_, v_es_3208_, v_j_3212_);
switch(lean_obj_tag(v_entry_3213_))
{
case 0:
{
lean_object* v_key_3214_; lean_object* v_expr_3215_; uint64_t v_configKey_3216_; lean_object* v_expr_3217_; uint64_t v_configKey_3218_; uint64_t v___x_3219_; uint64_t v___x_3220_; uint64_t v___x_3221_; uint64_t v___x_3222_; uint8_t v___x_3223_; 
v_key_3214_ = lean_ctor_get(v_entry_3213_, 0);
lean_inc(v_key_3214_);
lean_dec_ref_known(v_entry_3213_, 2);
v_expr_3215_ = lean_ctor_get(v_x_3207_, 0);
v_configKey_3216_ = lean_ctor_get_uint64(v_x_3207_, sizeof(void*)*1);
v_expr_3217_ = lean_ctor_get(v_key_3214_, 0);
lean_inc_ref(v_expr_3217_);
v_configKey_3218_ = lean_ctor_get_uint64(v_key_3214_, sizeof(void*)*1);
lean_dec(v_key_3214_);
v___x_3219_ = l_Lean_Expr_hash(v_expr_3215_);
v___x_3220_ = lean_uint64_mix_hash(v___x_3219_, v_configKey_3216_);
v___x_3221_ = l_Lean_Expr_hash(v_expr_3217_);
lean_dec_ref(v_expr_3217_);
v___x_3222_ = lean_uint64_mix_hash(v___x_3221_, v_configKey_3218_);
v___x_3223_ = lean_uint64_dec_eq(v___x_3220_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_dec(v_j_3212_);
return v_x_3205_;
}
else
{
lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3231_; 
lean_inc_ref(v_es_3208_);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_x_3205_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v_x_3205_, 0);
lean_dec(v_unused_3232_);
v___x_3225_ = v_x_3205_;
v_isShared_3226_ = v_isSharedCheck_3231_;
goto v_resetjp_3224_;
}
else
{
lean_dec(v_x_3205_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3231_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3227_ = lean_array_set(v_es_3208_, v_j_3212_, v___x_3209_);
lean_dec(v_j_3212_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3227_);
v___x_3229_ = v___x_3225_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
case 1:
{
lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3267_; 
lean_inc_ref(v_es_3208_);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_x_3205_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v_x_3205_, 0);
lean_dec(v_unused_3268_);
v___x_3234_ = v_x_3205_;
v_isShared_3235_ = v_isSharedCheck_3267_;
goto v_resetjp_3233_;
}
else
{
lean_dec(v_x_3205_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3267_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_node_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3266_; 
v_node_3236_ = lean_ctor_get(v_entry_3213_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_entry_3213_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3238_ = v_entry_3213_;
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_node_3236_);
lean_dec(v_entry_3213_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3266_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
size_t v___x_3240_; lean_object* v_entries_3241_; size_t v___x_3242_; lean_object* v_newNode_3243_; lean_object* v___x_3244_; 
v___x_3240_ = ((size_t)5ULL);
v_entries_3241_ = lean_array_set(v_es_3208_, v_j_3212_, v___x_3209_);
v___x_3242_ = lean_usize_shift_right(v_x_3206_, v___x_3240_);
v_newNode_3243_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_node_3236_, v___x_3242_, v_x_3207_);
lean_inc_ref(v_newNode_3243_);
v___x_3244_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_3243_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v___x_3246_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v_newNode_3243_);
v___x_3246_ = v___x_3238_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_newNode_3243_);
v___x_3246_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3247_ = lean_array_set(v_entries_3241_, v_j_3212_, v___x_3246_);
lean_dec(v_j_3212_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3247_);
v___x_3249_ = v___x_3234_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
else
{
lean_object* v_val_3252_; lean_object* v_fst_3253_; lean_object* v_snd_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_newNode_3243_);
lean_del_object(v___x_3238_);
v_val_3252_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_val_3252_);
lean_dec_ref_known(v___x_3244_, 1);
v_fst_3253_ = lean_ctor_get(v_val_3252_, 0);
v_snd_3254_ = lean_ctor_get(v_val_3252_, 1);
v_isSharedCheck_3265_ = !lean_is_exclusive(v_val_3252_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3256_ = v_val_3252_;
v_isShared_3257_ = v_isSharedCheck_3265_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_snd_3254_);
lean_inc(v_fst_3253_);
lean_dec(v_val_3252_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3265_;
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
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_fst_3253_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_snd_3254_);
v___x_3259_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3260_ = lean_array_set(v_entries_3241_, v_j_3212_, v___x_3259_);
lean_dec(v_j_3212_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3260_);
v___x_3262_ = v___x_3234_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_3212_);
return v_x_3205_;
}
}
}
else
{
lean_object* v_ks_3269_; lean_object* v_vs_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3284_; 
v_ks_3269_ = lean_ctor_get(v_x_3205_, 0);
v_vs_3270_ = lean_ctor_get(v_x_3205_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_x_3205_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3272_ = v_x_3205_;
v_isShared_3273_ = v_isSharedCheck_3284_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_vs_3270_);
lean_inc(v_ks_3269_);
lean_dec(v_x_3205_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3284_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5_spec__9(v_ks_3269_, v_x_3207_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3276_; 
if (v_isShared_3273_ == 0)
{
v___x_3276_ = v___x_3272_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_ks_3269_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_vs_3270_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
else
{
lean_object* v_val_3278_; lean_object* v_keys_x27_3279_; lean_object* v_vals_x27_3280_; lean_object* v___x_3282_; 
v_val_3278_ = lean_ctor_get(v___x_3274_, 0);
lean_inc_n(v_val_3278_, 2);
lean_dec_ref_known(v___x_3274_, 1);
v_keys_x27_3279_ = l_Array_eraseIdx___redArg(v_ks_3269_, v_val_3278_);
v_vals_x27_3280_ = l_Array_eraseIdx___redArg(v_vs_3270_, v_val_3278_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 1, v_vals_x27_3280_);
lean_ctor_set(v___x_3272_, 0, v_keys_x27_3279_);
v___x_3282_ = v___x_3272_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_keys_x27_3279_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_vals_x27_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg___boxed(lean_object* v_x_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
size_t v_x_4099__boxed_3288_; lean_object* v_res_3289_; 
v_x_4099__boxed_3288_ = lean_unbox_usize(v_x_3286_);
lean_dec(v_x_3286_);
v_res_3289_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3285_, v_x_4099__boxed_3288_, v_x_3287_);
lean_dec_ref(v_x_3287_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
lean_object* v_expr_3292_; uint64_t v_configKey_3293_; uint64_t v___x_3294_; uint64_t v___x_3295_; size_t v_h_3296_; lean_object* v___x_3297_; 
v_expr_3292_ = lean_ctor_get(v_x_3291_, 0);
v_configKey_3293_ = lean_ctor_get_uint64(v_x_3291_, sizeof(void*)*1);
v___x_3294_ = l_Lean_Expr_hash(v_expr_3292_);
v___x_3295_ = lean_uint64_mix_hash(v___x_3294_, v_configKey_3293_);
v_h_3296_ = lean_uint64_to_usize(v___x_3295_);
v___x_3297_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_3290_, v_h_3296_, v_x_3291_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg___boxed(lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_3298_, v_x_3299_);
lean_dec_ref(v_x_3299_);
return v_res_3300_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3303_ = l_Lean_stringToMessageData(v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
switch(lean_obj_tag(v_e_3304_))
{
case 0:
{
lean_object* v_deBruijnIndex_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_deBruijnIndex_3342_ = lean_ctor_get(v_e_3304_, 0);
lean_inc(v_deBruijnIndex_3342_);
lean_dec_ref_known(v_e_3304_, 1);
v___x_3343_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3344_ = l_Lean_mkBVar(v_deBruijnIndex_3342_);
v___x_3345_ = l_Lean_MessageData_ofExpr(v___x_3344_);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3343_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3346_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3347_;
}
case 1:
{
lean_object* v_fvarId_3348_; lean_object* v___x_3349_; 
v_fvarId_3348_ = lean_ctor_get(v_e_3304_, 0);
lean_inc(v_fvarId_3348_);
lean_dec_ref_known(v_e_3304_, 1);
v___x_3349_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3348_, v_a_3305_, v_a_3307_, v_a_3308_);
return v___x_3349_;
}
case 2:
{
lean_object* v_mvarId_3350_; lean_object* v___x_3351_; 
v_mvarId_3350_ = lean_ctor_get(v_e_3304_, 0);
lean_inc(v_mvarId_3350_);
lean_dec_ref_known(v_e_3304_, 1);
v___x_3351_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3350_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3351_;
}
case 3:
{
lean_object* v_u_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_u_3352_ = lean_ctor_get(v_e_3304_, 0);
lean_inc(v_u_3352_);
lean_dec_ref_known(v_e_3304_, 1);
v___x_3353_ = l_Lean_Level_succ___override(v_u_3352_);
v___x_3354_ = l_Lean_mkSort(v___x_3353_);
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
return v___x_3355_;
}
case 4:
{
lean_object* v_declName_3356_; lean_object* v_us_3357_; 
v_declName_3356_ = lean_ctor_get(v_e_3304_, 0);
lean_inc(v_declName_3356_);
v_us_3357_ = lean_ctor_get(v_e_3304_, 1);
lean_inc(v_us_3357_);
if (lean_obj_tag(v_us_3357_) == 0)
{
lean_object* v___x_3374_; 
lean_dec_ref_known(v_e_3304_, 2);
v___x_3374_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3356_, v_us_3357_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3374_;
}
else
{
uint8_t v_cacheInferType_3375_; 
v_cacheInferType_3375_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3375_ == 0)
{
lean_dec_ref_known(v_e_3304_, 2);
goto v___jp_3358_;
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = l_Lean_Expr_hasMVar(v_e_3304_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3483_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3483_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3483_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3437_; lean_object* v_cache_3438_; lean_object* v_inferType_3439_; lean_object* v___x_3440_; 
v___x_3437_ = lean_st_ref_get(v_a_3306_);
v_cache_3438_ = lean_ctor_get(v___x_3437_, 1);
lean_inc_ref(v_cache_3438_);
lean_dec(v___x_3437_);
v_inferType_3439_ = lean_ctor_get(v_cache_3438_, 0);
lean_inc_ref(v_inferType_3439_);
lean_dec_ref(v_cache_3438_);
v___x_3440_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3439_, v_a_3378_);
if (lean_obj_tag(v___x_3440_) == 1)
{
lean_object* v_val_3441_; lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v_expr_3444_; uint64_t v_configKey_3445_; lean_object* v_expr_3446_; uint64_t v_configKey_3447_; uint8_t v___x_3448_; 
v_val_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v_fst_3442_ = lean_ctor_get(v_val_3441_, 0);
lean_inc(v_fst_3442_);
v_snd_3443_ = lean_ctor_get(v_val_3441_, 1);
lean_inc(v_snd_3443_);
lean_dec(v_val_3441_);
v_expr_3444_ = lean_ctor_get(v_a_3378_, 0);
v_configKey_3445_ = lean_ctor_get_uint64(v_a_3378_, sizeof(void*)*1);
v_expr_3446_ = lean_ctor_get(v_fst_3442_, 0);
lean_inc_ref(v_expr_3446_);
v_configKey_3447_ = lean_ctor_get_uint64(v_fst_3442_, sizeof(void*)*1);
lean_dec(v_fst_3442_);
v___x_3448_ = lean_uint64_dec_eq(v_configKey_3445_, v_configKey_3447_);
if (v___x_3448_ == 0)
{
lean_dec_ref(v_expr_3446_);
lean_dec(v_snd_3443_);
lean_dec_ref(v_inferType_3439_);
lean_del_object(v___x_3380_);
goto v___jp_3423_;
}
else
{
size_t v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = ((size_t)64ULL);
v___x_3450_ = lean_expr_equal_budgeted(v_expr_3444_, v_expr_3446_, v___x_3449_);
lean_dec_ref(v_expr_3446_);
switch(v___x_3450_)
{
case 0:
{
lean_dec(v_snd_3443_);
lean_dec_ref(v_inferType_3439_);
lean_del_object(v___x_3380_);
goto v___jp_3423_;
}
case 1:
{
lean_object* v___x_3452_; 
lean_dec_ref(v_inferType_3439_);
lean_dec(v_a_3378_);
lean_dec(v_us_3357_);
lean_dec(v_declName_3356_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v_snd_3443_);
v___x_3452_ = v___x_3380_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_snd_3443_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
default: 
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v_cache_3456_; lean_object* v_mctx_3457_; lean_object* v_zetaDeltaFVarIds_3458_; lean_object* v_postponed_3459_; lean_object* v_diag_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v_snd_3443_);
lean_del_object(v___x_3380_);
v___x_3454_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3439_, v_a_3378_);
v___x_3455_ = lean_st_ref_take(v_a_3306_);
v_cache_3456_ = lean_ctor_get(v___x_3455_, 1);
v_mctx_3457_ = lean_ctor_get(v___x_3455_, 0);
v_zetaDeltaFVarIds_3458_ = lean_ctor_get(v___x_3455_, 2);
v_postponed_3459_ = lean_ctor_get(v___x_3455_, 3);
v_diag_3460_ = lean_ctor_get(v___x_3455_, 4);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3462_ = v___x_3455_;
v_isShared_3463_ = v_isSharedCheck_3482_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_diag_3460_);
lean_inc(v_postponed_3459_);
lean_inc(v_zetaDeltaFVarIds_3458_);
lean_inc(v_cache_3456_);
lean_inc(v_mctx_3457_);
lean_dec(v___x_3455_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3482_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v_funInfo_3464_; lean_object* v_synthInstance_3465_; lean_object* v_whnf_3466_; lean_object* v_defEqTrans_3467_; lean_object* v_defEqPerm_3468_; lean_object* v_unfold_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3480_; 
v_funInfo_3464_ = lean_ctor_get(v_cache_3456_, 1);
v_synthInstance_3465_ = lean_ctor_get(v_cache_3456_, 2);
v_whnf_3466_ = lean_ctor_get(v_cache_3456_, 3);
v_defEqTrans_3467_ = lean_ctor_get(v_cache_3456_, 4);
v_defEqPerm_3468_ = lean_ctor_get(v_cache_3456_, 5);
v_unfold_3469_ = lean_ctor_get(v_cache_3456_, 6);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_cache_3456_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; 
v_unused_3481_ = lean_ctor_get(v_cache_3456_, 0);
lean_dec(v_unused_3481_);
v___x_3471_ = v_cache_3456_;
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_unfold_3469_);
lean_inc(v_defEqPerm_3468_);
lean_inc(v_defEqTrans_3467_);
lean_inc(v_whnf_3466_);
lean_inc(v_synthInstance_3465_);
lean_inc(v_funInfo_3464_);
lean_dec(v_cache_3456_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3454_);
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_funInfo_3464_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_synthInstance_3465_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_whnf_3466_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_defEqTrans_3467_);
lean_ctor_set(v_reuseFailAlloc_3479_, 5, v_defEqPerm_3468_);
lean_ctor_set(v_reuseFailAlloc_3479_, 6, v_unfold_3469_);
v___x_3474_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 1, v___x_3474_);
v___x_3476_ = v___x_3462_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_mctx_3457_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_zetaDeltaFVarIds_3458_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_postponed_3459_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_diag_3460_);
v___x_3476_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; 
v___x_3477_ = lean_st_ref_put(v_a_3306_, v___x_3476_);
goto v___jp_3423_;
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
lean_dec(v___x_3440_);
lean_dec_ref(v_inferType_3439_);
lean_del_object(v___x_3380_);
goto v___jp_3423_;
}
v___jp_3382_:
{
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3356_, v_us_3357_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; uint8_t v___x_3385_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v___x_3385_ = l_Lean_Expr_hasMVar(v_a_3384_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3421_; 
lean_inc(v_a_3384_);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3421_ == 0)
{
lean_object* v_unused_3422_; 
v_unused_3422_ = lean_ctor_get(v___x_3383_, 0);
lean_dec(v_unused_3422_);
v___x_3387_ = v___x_3383_;
v_isShared_3388_ = v_isSharedCheck_3421_;
goto v_resetjp_3386_;
}
else
{
lean_dec(v___x_3383_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3421_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v_cache_3390_; lean_object* v_mctx_3391_; lean_object* v_zetaDeltaFVarIds_3392_; lean_object* v_postponed_3393_; lean_object* v_diag_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3420_; 
v___x_3389_ = lean_st_ref_take(v_a_3306_);
v_cache_3390_ = lean_ctor_get(v___x_3389_, 1);
v_mctx_3391_ = lean_ctor_get(v___x_3389_, 0);
v_zetaDeltaFVarIds_3392_ = lean_ctor_get(v___x_3389_, 2);
v_postponed_3393_ = lean_ctor_get(v___x_3389_, 3);
v_diag_3394_ = lean_ctor_get(v___x_3389_, 4);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3396_ = v___x_3389_;
v_isShared_3397_ = v_isSharedCheck_3420_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_diag_3394_);
lean_inc(v_postponed_3393_);
lean_inc(v_zetaDeltaFVarIds_3392_);
lean_inc(v_cache_3390_);
lean_inc(v_mctx_3391_);
lean_dec(v___x_3389_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3420_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_inferType_3398_; lean_object* v_funInfo_3399_; lean_object* v_synthInstance_3400_; lean_object* v_whnf_3401_; lean_object* v_defEqTrans_3402_; lean_object* v_defEqPerm_3403_; lean_object* v_unfold_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3419_; 
v_inferType_3398_ = lean_ctor_get(v_cache_3390_, 0);
v_funInfo_3399_ = lean_ctor_get(v_cache_3390_, 1);
v_synthInstance_3400_ = lean_ctor_get(v_cache_3390_, 2);
v_whnf_3401_ = lean_ctor_get(v_cache_3390_, 3);
v_defEqTrans_3402_ = lean_ctor_get(v_cache_3390_, 4);
v_defEqPerm_3403_ = lean_ctor_get(v_cache_3390_, 5);
v_unfold_3404_ = lean_ctor_get(v_cache_3390_, 6);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_cache_3390_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3406_ = v_cache_3390_;
v_isShared_3407_ = v_isSharedCheck_3419_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_unfold_3404_);
lean_inc(v_defEqPerm_3403_);
lean_inc(v_defEqTrans_3402_);
lean_inc(v_whnf_3401_);
lean_inc(v_synthInstance_3400_);
lean_inc(v_funInfo_3399_);
lean_inc(v_inferType_3398_);
lean_dec(v_cache_3390_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3419_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; lean_object* v___x_3410_; 
lean_inc(v_a_3384_);
v___x_3408_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3398_, v_a_3378_, v_a_3384_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3408_);
v___x_3410_ = v___x_3406_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_funInfo_3399_);
lean_ctor_set(v_reuseFailAlloc_3418_, 2, v_synthInstance_3400_);
lean_ctor_set(v_reuseFailAlloc_3418_, 3, v_whnf_3401_);
lean_ctor_set(v_reuseFailAlloc_3418_, 4, v_defEqTrans_3402_);
lean_ctor_set(v_reuseFailAlloc_3418_, 5, v_defEqPerm_3403_);
lean_ctor_set(v_reuseFailAlloc_3418_, 6, v_unfold_3404_);
v___x_3410_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3412_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v___x_3410_);
v___x_3412_ = v___x_3396_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_mctx_3391_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_zetaDeltaFVarIds_3392_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_postponed_3393_);
lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_diag_3394_);
v___x_3412_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = lean_st_ref_put(v_a_3306_, v___x_3412_);
if (v_isShared_3388_ == 0)
{
v___x_3415_ = v___x_3387_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3384_);
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
}
}
}
else
{
lean_dec(v_a_3378_);
return v___x_3383_;
}
}
else
{
lean_dec(v_a_3378_);
return v___x_3383_;
}
}
v___jp_3423_:
{
lean_object* v_toCold_3424_; lean_object* v_cancelTk_x3f_3425_; 
v_toCold_3424_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3425_ = lean_ctor_get(v_toCold_3424_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3425_) == 1)
{
lean_object* v_val_3426_; uint8_t v___x_3427_; 
v_val_3426_ = lean_ctor_get(v_cancelTk_x3f_3425_, 0);
v___x_3427_ = l_IO_CancelToken_isSet(v_val_3426_);
if (v___x_3427_ == 0)
{
goto v___jp_3382_;
}
else
{
lean_object* v___x_3428_; lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v_a_3378_);
lean_dec(v_us_3357_);
lean_dec(v_declName_3356_);
v___x_3428_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
goto v___jp_3382_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec(v_us_3357_);
lean_dec(v_declName_3356_);
v_a_3484_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3377_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3377_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3304_, 2);
goto v___jp_3358_;
}
}
}
v___jp_3358_:
{
lean_object* v_toCold_3359_; lean_object* v_cancelTk_x3f_3360_; 
v_toCold_3359_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3360_ = lean_ctor_get(v_toCold_3359_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3360_) == 1)
{
lean_object* v_val_3361_; uint8_t v___x_3362_; 
v_val_3361_ = lean_ctor_get(v_cancelTk_x3f_3360_, 0);
v___x_3362_ = l_IO_CancelToken_isSet(v_val_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; 
v___x_3363_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3356_, v_us_3357_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_us_3357_);
lean_dec(v_declName_3356_);
v___x_3364_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v___x_3373_; 
v___x_3373_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3356_, v_us_3357_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3373_;
}
}
}
case 5:
{
lean_object* v_fn_3492_; uint8_t v_cacheInferType_3493_; lean_object* v_nargs_3494_; lean_object* v___x_3495_; lean_object* v_dummy_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_fn_3492_ = lean_ctor_get(v_e_3304_, 0);
v_cacheInferType_3493_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*7 + 3);
v_nargs_3494_ = l_Lean_Expr_getAppNumArgs(v_e_3304_);
v___x_3495_ = l_Lean_Expr_getAppFn(v_fn_3492_);
v_dummy_3496_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3494_);
v___x_3497_ = lean_mk_array(v_nargs_3494_, v_dummy_3496_);
v___x_3498_ = lean_unsigned_to_nat(1u);
v___x_3499_ = lean_nat_sub(v_nargs_3494_, v___x_3498_);
lean_dec(v_nargs_3494_);
lean_inc_ref(v_e_3304_);
v___x_3500_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3304_, v___x_3497_, v___x_3499_);
if (v_cacheInferType_3493_ == 0)
{
lean_dec_ref_known(v_e_3304_, 2);
goto v___jp_3501_;
}
else
{
uint8_t v___x_3517_; 
v___x_3517_ = l_Lean_Expr_hasMVar(v_e_3304_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3624_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3624_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3624_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3578_; lean_object* v_cache_3579_; lean_object* v_inferType_3580_; lean_object* v___x_3581_; 
v___x_3578_ = lean_st_ref_get(v_a_3306_);
v_cache_3579_ = lean_ctor_get(v___x_3578_, 1);
lean_inc_ref(v_cache_3579_);
lean_dec(v___x_3578_);
v_inferType_3580_ = lean_ctor_get(v_cache_3579_, 0);
lean_inc_ref(v_inferType_3580_);
lean_dec_ref(v_cache_3579_);
v___x_3581_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3580_, v_a_3519_);
if (lean_obj_tag(v___x_3581_) == 1)
{
lean_object* v_val_3582_; lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v_expr_3585_; uint64_t v_configKey_3586_; lean_object* v_expr_3587_; uint64_t v_configKey_3588_; uint8_t v___x_3589_; 
v_val_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v_fst_3583_ = lean_ctor_get(v_val_3582_, 0);
lean_inc(v_fst_3583_);
v_snd_3584_ = lean_ctor_get(v_val_3582_, 1);
lean_inc(v_snd_3584_);
lean_dec(v_val_3582_);
v_expr_3585_ = lean_ctor_get(v_a_3519_, 0);
v_configKey_3586_ = lean_ctor_get_uint64(v_a_3519_, sizeof(void*)*1);
v_expr_3587_ = lean_ctor_get(v_fst_3583_, 0);
lean_inc_ref(v_expr_3587_);
v_configKey_3588_ = lean_ctor_get_uint64(v_fst_3583_, sizeof(void*)*1);
lean_dec(v_fst_3583_);
v___x_3589_ = lean_uint64_dec_eq(v_configKey_3586_, v_configKey_3588_);
if (v___x_3589_ == 0)
{
lean_dec_ref(v_expr_3587_);
lean_dec(v_snd_3584_);
lean_dec_ref(v_inferType_3580_);
lean_del_object(v___x_3521_);
goto v___jp_3564_;
}
else
{
size_t v___x_3590_; uint8_t v___x_3591_; 
v___x_3590_ = ((size_t)64ULL);
v___x_3591_ = lean_expr_equal_budgeted(v_expr_3585_, v_expr_3587_, v___x_3590_);
lean_dec_ref(v_expr_3587_);
switch(v___x_3591_)
{
case 0:
{
lean_dec(v_snd_3584_);
lean_dec_ref(v_inferType_3580_);
lean_del_object(v___x_3521_);
goto v___jp_3564_;
}
case 1:
{
lean_object* v___x_3593_; 
lean_dec_ref(v_inferType_3580_);
lean_dec(v_a_3519_);
lean_dec_ref(v___x_3500_);
lean_dec_ref(v___x_3495_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v_snd_3584_);
v___x_3593_ = v___x_3521_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_snd_3584_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
default: 
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_cache_3597_; lean_object* v_mctx_3598_; lean_object* v_zetaDeltaFVarIds_3599_; lean_object* v_postponed_3600_; lean_object* v_diag_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_snd_3584_);
lean_del_object(v___x_3521_);
v___x_3595_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3580_, v_a_3519_);
v___x_3596_ = lean_st_ref_take(v_a_3306_);
v_cache_3597_ = lean_ctor_get(v___x_3596_, 1);
v_mctx_3598_ = lean_ctor_get(v___x_3596_, 0);
v_zetaDeltaFVarIds_3599_ = lean_ctor_get(v___x_3596_, 2);
v_postponed_3600_ = lean_ctor_get(v___x_3596_, 3);
v_diag_3601_ = lean_ctor_get(v___x_3596_, 4);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3603_ = v___x_3596_;
v_isShared_3604_ = v_isSharedCheck_3623_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_diag_3601_);
lean_inc(v_postponed_3600_);
lean_inc(v_zetaDeltaFVarIds_3599_);
lean_inc(v_cache_3597_);
lean_inc(v_mctx_3598_);
lean_dec(v___x_3596_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3623_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_funInfo_3605_; lean_object* v_synthInstance_3606_; lean_object* v_whnf_3607_; lean_object* v_defEqTrans_3608_; lean_object* v_defEqPerm_3609_; lean_object* v_unfold_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3621_; 
v_funInfo_3605_ = lean_ctor_get(v_cache_3597_, 1);
v_synthInstance_3606_ = lean_ctor_get(v_cache_3597_, 2);
v_whnf_3607_ = lean_ctor_get(v_cache_3597_, 3);
v_defEqTrans_3608_ = lean_ctor_get(v_cache_3597_, 4);
v_defEqPerm_3609_ = lean_ctor_get(v_cache_3597_, 5);
v_unfold_3610_ = lean_ctor_get(v_cache_3597_, 6);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_cache_3597_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v_cache_3597_, 0);
lean_dec(v_unused_3622_);
v___x_3612_ = v_cache_3597_;
v_isShared_3613_ = v_isSharedCheck_3621_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_unfold_3610_);
lean_inc(v_defEqPerm_3609_);
lean_inc(v_defEqTrans_3608_);
lean_inc(v_whnf_3607_);
lean_inc(v_synthInstance_3606_);
lean_inc(v_funInfo_3605_);
lean_dec(v_cache_3597_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3621_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v___x_3595_);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_funInfo_3605_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_synthInstance_3606_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_whnf_3607_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v_defEqTrans_3608_);
lean_ctor_set(v_reuseFailAlloc_3620_, 5, v_defEqPerm_3609_);
lean_ctor_set(v_reuseFailAlloc_3620_, 6, v_unfold_3610_);
v___x_3615_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 1, v___x_3615_);
v___x_3617_ = v___x_3603_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_mctx_3598_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_zetaDeltaFVarIds_3599_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_postponed_3600_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_diag_3601_);
v___x_3617_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; 
v___x_3618_ = lean_st_ref_put(v_a_3306_, v___x_3617_);
goto v___jp_3564_;
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
lean_dec(v___x_3581_);
lean_dec_ref(v_inferType_3580_);
lean_del_object(v___x_3521_);
goto v___jp_3564_;
}
v___jp_3523_:
{
lean_object* v___x_3524_; 
v___x_3524_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3495_, v___x_3500_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec_ref(v___x_3500_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; uint8_t v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v___x_3526_ = l_Lean_Expr_hasMVar(v_a_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3562_; 
lean_inc(v_a_3525_);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v___x_3524_, 0);
lean_dec(v_unused_3563_);
v___x_3528_ = v___x_3524_;
v_isShared_3529_ = v_isSharedCheck_3562_;
goto v_resetjp_3527_;
}
else
{
lean_dec(v___x_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3562_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v_cache_3531_; lean_object* v_mctx_3532_; lean_object* v_zetaDeltaFVarIds_3533_; lean_object* v_postponed_3534_; lean_object* v_diag_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3561_; 
v___x_3530_ = lean_st_ref_take(v_a_3306_);
v_cache_3531_ = lean_ctor_get(v___x_3530_, 1);
v_mctx_3532_ = lean_ctor_get(v___x_3530_, 0);
v_zetaDeltaFVarIds_3533_ = lean_ctor_get(v___x_3530_, 2);
v_postponed_3534_ = lean_ctor_get(v___x_3530_, 3);
v_diag_3535_ = lean_ctor_get(v___x_3530_, 4);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3537_ = v___x_3530_;
v_isShared_3538_ = v_isSharedCheck_3561_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_diag_3535_);
lean_inc(v_postponed_3534_);
lean_inc(v_zetaDeltaFVarIds_3533_);
lean_inc(v_cache_3531_);
lean_inc(v_mctx_3532_);
lean_dec(v___x_3530_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3561_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v_inferType_3539_; lean_object* v_funInfo_3540_; lean_object* v_synthInstance_3541_; lean_object* v_whnf_3542_; lean_object* v_defEqTrans_3543_; lean_object* v_defEqPerm_3544_; lean_object* v_unfold_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3560_; 
v_inferType_3539_ = lean_ctor_get(v_cache_3531_, 0);
v_funInfo_3540_ = lean_ctor_get(v_cache_3531_, 1);
v_synthInstance_3541_ = lean_ctor_get(v_cache_3531_, 2);
v_whnf_3542_ = lean_ctor_get(v_cache_3531_, 3);
v_defEqTrans_3543_ = lean_ctor_get(v_cache_3531_, 4);
v_defEqPerm_3544_ = lean_ctor_get(v_cache_3531_, 5);
v_unfold_3545_ = lean_ctor_get(v_cache_3531_, 6);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_cache_3531_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3547_ = v_cache_3531_;
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_unfold_3545_);
lean_inc(v_defEqPerm_3544_);
lean_inc(v_defEqTrans_3543_);
lean_inc(v_whnf_3542_);
lean_inc(v_synthInstance_3541_);
lean_inc(v_funInfo_3540_);
lean_inc(v_inferType_3539_);
lean_dec(v_cache_3531_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_inc(v_a_3525_);
v___x_3549_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3539_, v_a_3519_, v_a_3525_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3549_);
v___x_3551_ = v___x_3547_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_funInfo_3540_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_synthInstance_3541_);
lean_ctor_set(v_reuseFailAlloc_3559_, 3, v_whnf_3542_);
lean_ctor_set(v_reuseFailAlloc_3559_, 4, v_defEqTrans_3543_);
lean_ctor_set(v_reuseFailAlloc_3559_, 5, v_defEqPerm_3544_);
lean_ctor_set(v_reuseFailAlloc_3559_, 6, v_unfold_3545_);
v___x_3551_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 1, v___x_3551_);
v___x_3553_ = v___x_3537_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_mctx_3532_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_zetaDeltaFVarIds_3533_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_postponed_3534_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_diag_3535_);
v___x_3553_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3554_ = lean_st_ref_put(v_a_3306_, v___x_3553_);
if (v_isShared_3529_ == 0)
{
v___x_3556_ = v___x_3528_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3525_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3519_);
return v___x_3524_;
}
}
else
{
lean_dec(v_a_3519_);
return v___x_3524_;
}
}
v___jp_3564_:
{
lean_object* v_toCold_3565_; lean_object* v_cancelTk_x3f_3566_; 
v_toCold_3565_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3566_ = lean_ctor_get(v_toCold_3565_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3566_) == 1)
{
lean_object* v_val_3567_; uint8_t v___x_3568_; 
v_val_3567_ = lean_ctor_get(v_cancelTk_x3f_3566_, 0);
v___x_3568_ = l_IO_CancelToken_isSet(v_val_3567_);
if (v___x_3568_ == 0)
{
goto v___jp_3523_;
}
else
{
lean_object* v___x_3569_; lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v_a_3519_);
lean_dec_ref(v___x_3500_);
lean_dec_ref(v___x_3495_);
v___x_3569_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
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
else
{
goto v___jp_3523_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v___x_3500_);
lean_dec_ref(v___x_3495_);
v_a_3625_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3518_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3518_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3304_, 2);
goto v___jp_3501_;
}
}
v___jp_3501_:
{
lean_object* v_toCold_3502_; lean_object* v_cancelTk_x3f_3503_; 
v_toCold_3502_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3503_ = lean_ctor_get(v_toCold_3502_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3503_) == 1)
{
lean_object* v_val_3504_; uint8_t v___x_3505_; 
v_val_3504_ = lean_ctor_get(v_cancelTk_x3f_3503_, 0);
v___x_3505_ = l_IO_CancelToken_isSet(v_val_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
v___x_3506_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3495_, v___x_3500_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec_ref(v___x_3500_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v___x_3500_);
lean_dec_ref(v___x_3495_);
v___x_3507_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v___x_3516_; 
v___x_3516_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3495_, v___x_3500_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
lean_dec_ref(v___x_3500_);
return v___x_3516_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3633_; 
v_cacheInferType_3633_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3633_ == 0)
{
goto v___jp_3310_;
}
else
{
uint8_t v___x_3634_; 
v___x_3634_ = l_Lean_Expr_hasMVar(v_e_3304_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
lean_inc_ref(v_e_3304_);
v___x_3635_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3741_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3741_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3741_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3695_; lean_object* v_cache_3696_; lean_object* v_inferType_3697_; lean_object* v___x_3698_; 
v___x_3695_ = lean_st_ref_get(v_a_3306_);
v_cache_3696_ = lean_ctor_get(v___x_3695_, 1);
lean_inc_ref(v_cache_3696_);
lean_dec(v___x_3695_);
v_inferType_3697_ = lean_ctor_get(v_cache_3696_, 0);
lean_inc_ref(v_inferType_3697_);
lean_dec_ref(v_cache_3696_);
v___x_3698_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3697_, v_a_3636_);
if (lean_obj_tag(v___x_3698_) == 1)
{
lean_object* v_val_3699_; lean_object* v_fst_3700_; lean_object* v_snd_3701_; lean_object* v_expr_3702_; uint64_t v_configKey_3703_; lean_object* v_expr_3704_; uint64_t v_configKey_3705_; uint8_t v___x_3706_; 
v_val_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v_fst_3700_ = lean_ctor_get(v_val_3699_, 0);
lean_inc(v_fst_3700_);
v_snd_3701_ = lean_ctor_get(v_val_3699_, 1);
lean_inc(v_snd_3701_);
lean_dec(v_val_3699_);
v_expr_3702_ = lean_ctor_get(v_a_3636_, 0);
v_configKey_3703_ = lean_ctor_get_uint64(v_a_3636_, sizeof(void*)*1);
v_expr_3704_ = lean_ctor_get(v_fst_3700_, 0);
lean_inc_ref(v_expr_3704_);
v_configKey_3705_ = lean_ctor_get_uint64(v_fst_3700_, sizeof(void*)*1);
lean_dec(v_fst_3700_);
v___x_3706_ = lean_uint64_dec_eq(v_configKey_3703_, v_configKey_3705_);
if (v___x_3706_ == 0)
{
lean_dec_ref(v_expr_3704_);
lean_dec(v_snd_3701_);
lean_dec_ref(v_inferType_3697_);
lean_del_object(v___x_3638_);
goto v___jp_3681_;
}
else
{
size_t v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = ((size_t)64ULL);
v___x_3708_ = lean_expr_equal_budgeted(v_expr_3702_, v_expr_3704_, v___x_3707_);
lean_dec_ref(v_expr_3704_);
switch(v___x_3708_)
{
case 0:
{
lean_dec(v_snd_3701_);
lean_dec_ref(v_inferType_3697_);
lean_del_object(v___x_3638_);
goto v___jp_3681_;
}
case 1:
{
lean_object* v___x_3710_; 
lean_dec_ref(v_inferType_3697_);
lean_dec(v_a_3636_);
lean_dec_ref_known(v_e_3304_, 3);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v_snd_3701_);
v___x_3710_ = v___x_3638_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_snd_3701_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
default: 
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v_cache_3714_; lean_object* v_mctx_3715_; lean_object* v_zetaDeltaFVarIds_3716_; lean_object* v_postponed_3717_; lean_object* v_diag_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v_snd_3701_);
lean_del_object(v___x_3638_);
v___x_3712_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3697_, v_a_3636_);
v___x_3713_ = lean_st_ref_take(v_a_3306_);
v_cache_3714_ = lean_ctor_get(v___x_3713_, 1);
v_mctx_3715_ = lean_ctor_get(v___x_3713_, 0);
v_zetaDeltaFVarIds_3716_ = lean_ctor_get(v___x_3713_, 2);
v_postponed_3717_ = lean_ctor_get(v___x_3713_, 3);
v_diag_3718_ = lean_ctor_get(v___x_3713_, 4);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3720_ = v___x_3713_;
v_isShared_3721_ = v_isSharedCheck_3740_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_diag_3718_);
lean_inc(v_postponed_3717_);
lean_inc(v_zetaDeltaFVarIds_3716_);
lean_inc(v_cache_3714_);
lean_inc(v_mctx_3715_);
lean_dec(v___x_3713_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3740_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_funInfo_3722_; lean_object* v_synthInstance_3723_; lean_object* v_whnf_3724_; lean_object* v_defEqTrans_3725_; lean_object* v_defEqPerm_3726_; lean_object* v_unfold_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3738_; 
v_funInfo_3722_ = lean_ctor_get(v_cache_3714_, 1);
v_synthInstance_3723_ = lean_ctor_get(v_cache_3714_, 2);
v_whnf_3724_ = lean_ctor_get(v_cache_3714_, 3);
v_defEqTrans_3725_ = lean_ctor_get(v_cache_3714_, 4);
v_defEqPerm_3726_ = lean_ctor_get(v_cache_3714_, 5);
v_unfold_3727_ = lean_ctor_get(v_cache_3714_, 6);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_cache_3714_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; 
v_unused_3739_ = lean_ctor_get(v_cache_3714_, 0);
lean_dec(v_unused_3739_);
v___x_3729_ = v_cache_3714_;
v_isShared_3730_ = v_isSharedCheck_3738_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_unfold_3727_);
lean_inc(v_defEqPerm_3726_);
lean_inc(v_defEqTrans_3725_);
lean_inc(v_whnf_3724_);
lean_inc(v_synthInstance_3723_);
lean_inc(v_funInfo_3722_);
lean_dec(v_cache_3714_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3738_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3712_);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_funInfo_3722_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_synthInstance_3723_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_whnf_3724_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_defEqTrans_3725_);
lean_ctor_set(v_reuseFailAlloc_3737_, 5, v_defEqPerm_3726_);
lean_ctor_set(v_reuseFailAlloc_3737_, 6, v_unfold_3727_);
v___x_3732_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_object* v___x_3734_; 
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 1, v___x_3732_);
v___x_3734_ = v___x_3720_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_mctx_3715_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v_zetaDeltaFVarIds_3716_);
lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_postponed_3717_);
lean_ctor_set(v_reuseFailAlloc_3736_, 4, v_diag_3718_);
v___x_3734_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_st_ref_put(v_a_3306_, v___x_3734_);
goto v___jp_3681_;
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
lean_dec(v___x_3698_);
lean_dec_ref(v_inferType_3697_);
lean_del_object(v___x_3638_);
goto v___jp_3681_;
}
v___jp_3640_:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; uint8_t v___x_3643_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v___x_3643_ = l_Lean_Expr_hasMVar(v_a_3642_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3679_; 
lean_inc(v_a_3642_);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3679_ == 0)
{
lean_object* v_unused_3680_; 
v_unused_3680_ = lean_ctor_get(v___x_3641_, 0);
lean_dec(v_unused_3680_);
v___x_3645_ = v___x_3641_;
v_isShared_3646_ = v_isSharedCheck_3679_;
goto v_resetjp_3644_;
}
else
{
lean_dec(v___x_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3679_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v_cache_3648_; lean_object* v_mctx_3649_; lean_object* v_zetaDeltaFVarIds_3650_; lean_object* v_postponed_3651_; lean_object* v_diag_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3678_; 
v___x_3647_ = lean_st_ref_take(v_a_3306_);
v_cache_3648_ = lean_ctor_get(v___x_3647_, 1);
v_mctx_3649_ = lean_ctor_get(v___x_3647_, 0);
v_zetaDeltaFVarIds_3650_ = lean_ctor_get(v___x_3647_, 2);
v_postponed_3651_ = lean_ctor_get(v___x_3647_, 3);
v_diag_3652_ = lean_ctor_get(v___x_3647_, 4);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3654_ = v___x_3647_;
v_isShared_3655_ = v_isSharedCheck_3678_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_diag_3652_);
lean_inc(v_postponed_3651_);
lean_inc(v_zetaDeltaFVarIds_3650_);
lean_inc(v_cache_3648_);
lean_inc(v_mctx_3649_);
lean_dec(v___x_3647_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3678_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_inferType_3656_; lean_object* v_funInfo_3657_; lean_object* v_synthInstance_3658_; lean_object* v_whnf_3659_; lean_object* v_defEqTrans_3660_; lean_object* v_defEqPerm_3661_; lean_object* v_unfold_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3677_; 
v_inferType_3656_ = lean_ctor_get(v_cache_3648_, 0);
v_funInfo_3657_ = lean_ctor_get(v_cache_3648_, 1);
v_synthInstance_3658_ = lean_ctor_get(v_cache_3648_, 2);
v_whnf_3659_ = lean_ctor_get(v_cache_3648_, 3);
v_defEqTrans_3660_ = lean_ctor_get(v_cache_3648_, 4);
v_defEqPerm_3661_ = lean_ctor_get(v_cache_3648_, 5);
v_unfold_3662_ = lean_ctor_get(v_cache_3648_, 6);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_cache_3648_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3664_ = v_cache_3648_;
v_isShared_3665_ = v_isSharedCheck_3677_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_unfold_3662_);
lean_inc(v_defEqPerm_3661_);
lean_inc(v_defEqTrans_3660_);
lean_inc(v_whnf_3659_);
lean_inc(v_synthInstance_3658_);
lean_inc(v_funInfo_3657_);
lean_inc(v_inferType_3656_);
lean_dec(v_cache_3648_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3677_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
lean_inc(v_a_3642_);
v___x_3666_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3656_, v_a_3636_, v_a_3642_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3666_);
v___x_3668_ = v___x_3664_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_funInfo_3657_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_synthInstance_3658_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_whnf_3659_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_defEqTrans_3660_);
lean_ctor_set(v_reuseFailAlloc_3676_, 5, v_defEqPerm_3661_);
lean_ctor_set(v_reuseFailAlloc_3676_, 6, v_unfold_3662_);
v___x_3668_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3670_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 1, v___x_3668_);
v___x_3670_ = v___x_3654_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_mctx_3649_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_zetaDeltaFVarIds_3650_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v_postponed_3651_);
lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_diag_3652_);
v___x_3670_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3671_ = lean_st_ref_put(v_a_3306_, v___x_3670_);
if (v_isShared_3646_ == 0)
{
v___x_3673_ = v___x_3645_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3642_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3636_);
return v___x_3641_;
}
}
else
{
lean_dec(v_a_3636_);
return v___x_3641_;
}
}
v___jp_3681_:
{
lean_object* v_toCold_3682_; lean_object* v_cancelTk_x3f_3683_; 
v_toCold_3682_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3683_ = lean_ctor_get(v_toCold_3682_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3683_) == 1)
{
lean_object* v_val_3684_; uint8_t v___x_3685_; 
v_val_3684_ = lean_ctor_get(v_cancelTk_x3f_3683_, 0);
v___x_3685_ = l_IO_CancelToken_isSet(v_val_3684_);
if (v___x_3685_ == 0)
{
goto v___jp_3640_;
}
else
{
lean_object* v___x_3686_; lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_a_3636_);
lean_dec_ref_known(v_e_3304_, 3);
v___x_3686_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
goto v___jp_3640_;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref_known(v_e_3304_, 3);
v_a_3742_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3635_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3635_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
goto v___jp_3310_;
}
}
}
case 9:
{
lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_a_3750_ = lean_ctor_get(v_e_3304_, 0);
lean_inc_ref(v_a_3750_);
lean_dec_ref_known(v_e_3304_, 1);
v___x_3751_ = l_Lean_Literal_type(v_a_3750_);
lean_dec_ref(v_a_3750_);
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
return v___x_3752_;
}
case 10:
{
lean_object* v_expr_3753_; 
v_expr_3753_ = lean_ctor_get(v_e_3304_, 1);
lean_inc_ref(v_expr_3753_);
lean_dec_ref_known(v_e_3304_, 2);
v_e_3304_ = v_expr_3753_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3755_; lean_object* v_idx_3756_; lean_object* v_struct_3757_; uint8_t v_cacheInferType_3774_; 
v_typeName_3755_ = lean_ctor_get(v_e_3304_, 0);
lean_inc(v_typeName_3755_);
v_idx_3756_ = lean_ctor_get(v_e_3304_, 1);
lean_inc(v_idx_3756_);
v_struct_3757_ = lean_ctor_get(v_e_3304_, 2);
lean_inc_ref(v_struct_3757_);
v_cacheInferType_3774_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3774_ == 0)
{
lean_dec_ref_known(v_e_3304_, 3);
goto v___jp_3758_;
}
else
{
uint8_t v___x_3775_; 
v___x_3775_ = l_Lean_Expr_hasMVar(v_e_3304_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3882_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3779_ = v___x_3776_;
v_isShared_3780_ = v_isSharedCheck_3882_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3882_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3836_; lean_object* v_cache_3837_; lean_object* v_inferType_3838_; lean_object* v___x_3839_; 
v___x_3836_ = lean_st_ref_get(v_a_3306_);
v_cache_3837_ = lean_ctor_get(v___x_3836_, 1);
lean_inc_ref(v_cache_3837_);
lean_dec(v___x_3836_);
v_inferType_3838_ = lean_ctor_get(v_cache_3837_, 0);
lean_inc_ref(v_inferType_3838_);
lean_dec_ref(v_cache_3837_);
v___x_3839_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3838_, v_a_3777_);
if (lean_obj_tag(v___x_3839_) == 1)
{
lean_object* v_val_3840_; lean_object* v_fst_3841_; lean_object* v_snd_3842_; lean_object* v_expr_3843_; uint64_t v_configKey_3844_; lean_object* v_expr_3845_; uint64_t v_configKey_3846_; uint8_t v___x_3847_; 
v_val_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_val_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v_fst_3841_ = lean_ctor_get(v_val_3840_, 0);
lean_inc(v_fst_3841_);
v_snd_3842_ = lean_ctor_get(v_val_3840_, 1);
lean_inc(v_snd_3842_);
lean_dec(v_val_3840_);
v_expr_3843_ = lean_ctor_get(v_a_3777_, 0);
v_configKey_3844_ = lean_ctor_get_uint64(v_a_3777_, sizeof(void*)*1);
v_expr_3845_ = lean_ctor_get(v_fst_3841_, 0);
lean_inc_ref(v_expr_3845_);
v_configKey_3846_ = lean_ctor_get_uint64(v_fst_3841_, sizeof(void*)*1);
lean_dec(v_fst_3841_);
v___x_3847_ = lean_uint64_dec_eq(v_configKey_3844_, v_configKey_3846_);
if (v___x_3847_ == 0)
{
lean_dec_ref(v_expr_3845_);
lean_dec(v_snd_3842_);
lean_dec_ref(v_inferType_3838_);
lean_del_object(v___x_3779_);
goto v___jp_3822_;
}
else
{
size_t v___x_3848_; uint8_t v___x_3849_; 
v___x_3848_ = ((size_t)64ULL);
v___x_3849_ = lean_expr_equal_budgeted(v_expr_3843_, v_expr_3845_, v___x_3848_);
lean_dec_ref(v_expr_3845_);
switch(v___x_3849_)
{
case 0:
{
lean_dec(v_snd_3842_);
lean_dec_ref(v_inferType_3838_);
lean_del_object(v___x_3779_);
goto v___jp_3822_;
}
case 1:
{
lean_object* v___x_3851_; 
lean_dec_ref(v_inferType_3838_);
lean_dec(v_a_3777_);
lean_dec_ref(v_struct_3757_);
lean_dec(v_idx_3756_);
lean_dec(v_typeName_3755_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v_snd_3842_);
v___x_3851_ = v___x_3779_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_snd_3842_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
default: 
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v_cache_3855_; lean_object* v_mctx_3856_; lean_object* v_zetaDeltaFVarIds_3857_; lean_object* v_postponed_3858_; lean_object* v_diag_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_snd_3842_);
lean_del_object(v___x_3779_);
v___x_3853_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3838_, v_a_3777_);
v___x_3854_ = lean_st_ref_take(v_a_3306_);
v_cache_3855_ = lean_ctor_get(v___x_3854_, 1);
v_mctx_3856_ = lean_ctor_get(v___x_3854_, 0);
v_zetaDeltaFVarIds_3857_ = lean_ctor_get(v___x_3854_, 2);
v_postponed_3858_ = lean_ctor_get(v___x_3854_, 3);
v_diag_3859_ = lean_ctor_get(v___x_3854_, 4);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3861_ = v___x_3854_;
v_isShared_3862_ = v_isSharedCheck_3881_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_diag_3859_);
lean_inc(v_postponed_3858_);
lean_inc(v_zetaDeltaFVarIds_3857_);
lean_inc(v_cache_3855_);
lean_inc(v_mctx_3856_);
lean_dec(v___x_3854_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3881_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_funInfo_3863_; lean_object* v_synthInstance_3864_; lean_object* v_whnf_3865_; lean_object* v_defEqTrans_3866_; lean_object* v_defEqPerm_3867_; lean_object* v_unfold_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3879_; 
v_funInfo_3863_ = lean_ctor_get(v_cache_3855_, 1);
v_synthInstance_3864_ = lean_ctor_get(v_cache_3855_, 2);
v_whnf_3865_ = lean_ctor_get(v_cache_3855_, 3);
v_defEqTrans_3866_ = lean_ctor_get(v_cache_3855_, 4);
v_defEqPerm_3867_ = lean_ctor_get(v_cache_3855_, 5);
v_unfold_3868_ = lean_ctor_get(v_cache_3855_, 6);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_cache_3855_);
if (v_isSharedCheck_3879_ == 0)
{
lean_object* v_unused_3880_; 
v_unused_3880_ = lean_ctor_get(v_cache_3855_, 0);
lean_dec(v_unused_3880_);
v___x_3870_ = v_cache_3855_;
v_isShared_3871_ = v_isSharedCheck_3879_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_unfold_3868_);
lean_inc(v_defEqPerm_3867_);
lean_inc(v_defEqTrans_3866_);
lean_inc(v_whnf_3865_);
lean_inc(v_synthInstance_3864_);
lean_inc(v_funInfo_3863_);
lean_dec(v_cache_3855_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3879_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3853_);
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_funInfo_3863_);
lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_synthInstance_3864_);
lean_ctor_set(v_reuseFailAlloc_3878_, 3, v_whnf_3865_);
lean_ctor_set(v_reuseFailAlloc_3878_, 4, v_defEqTrans_3866_);
lean_ctor_set(v_reuseFailAlloc_3878_, 5, v_defEqPerm_3867_);
lean_ctor_set(v_reuseFailAlloc_3878_, 6, v_unfold_3868_);
v___x_3873_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3875_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v___x_3873_);
v___x_3875_ = v___x_3861_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_mctx_3856_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v___x_3873_);
lean_ctor_set(v_reuseFailAlloc_3877_, 2, v_zetaDeltaFVarIds_3857_);
lean_ctor_set(v_reuseFailAlloc_3877_, 3, v_postponed_3858_);
lean_ctor_set(v_reuseFailAlloc_3877_, 4, v_diag_3859_);
v___x_3875_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_st_ref_put(v_a_3306_, v___x_3875_);
goto v___jp_3822_;
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
lean_dec(v___x_3839_);
lean_dec_ref(v_inferType_3838_);
lean_del_object(v___x_3779_);
goto v___jp_3822_;
}
v___jp_3781_:
{
lean_object* v___x_3782_; 
v___x_3782_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3755_, v_idx_3756_, v_struct_3757_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; uint8_t v___x_3784_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v___x_3784_ = l_Lean_Expr_hasMVar(v_a_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3820_; 
lean_inc(v_a_3783_);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v___x_3782_, 0);
lean_dec(v_unused_3821_);
v___x_3786_ = v___x_3782_;
v_isShared_3787_ = v_isSharedCheck_3820_;
goto v_resetjp_3785_;
}
else
{
lean_dec(v___x_3782_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3820_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3788_; lean_object* v_cache_3789_; lean_object* v_mctx_3790_; lean_object* v_zetaDeltaFVarIds_3791_; lean_object* v_postponed_3792_; lean_object* v_diag_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3819_; 
v___x_3788_ = lean_st_ref_take(v_a_3306_);
v_cache_3789_ = lean_ctor_get(v___x_3788_, 1);
v_mctx_3790_ = lean_ctor_get(v___x_3788_, 0);
v_zetaDeltaFVarIds_3791_ = lean_ctor_get(v___x_3788_, 2);
v_postponed_3792_ = lean_ctor_get(v___x_3788_, 3);
v_diag_3793_ = lean_ctor_get(v___x_3788_, 4);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3795_ = v___x_3788_;
v_isShared_3796_ = v_isSharedCheck_3819_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_diag_3793_);
lean_inc(v_postponed_3792_);
lean_inc(v_zetaDeltaFVarIds_3791_);
lean_inc(v_cache_3789_);
lean_inc(v_mctx_3790_);
lean_dec(v___x_3788_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3819_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v_inferType_3797_; lean_object* v_funInfo_3798_; lean_object* v_synthInstance_3799_; lean_object* v_whnf_3800_; lean_object* v_defEqTrans_3801_; lean_object* v_defEqPerm_3802_; lean_object* v_unfold_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3818_; 
v_inferType_3797_ = lean_ctor_get(v_cache_3789_, 0);
v_funInfo_3798_ = lean_ctor_get(v_cache_3789_, 1);
v_synthInstance_3799_ = lean_ctor_get(v_cache_3789_, 2);
v_whnf_3800_ = lean_ctor_get(v_cache_3789_, 3);
v_defEqTrans_3801_ = lean_ctor_get(v_cache_3789_, 4);
v_defEqPerm_3802_ = lean_ctor_get(v_cache_3789_, 5);
v_unfold_3803_ = lean_ctor_get(v_cache_3789_, 6);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_cache_3789_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3805_ = v_cache_3789_;
v_isShared_3806_ = v_isSharedCheck_3818_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_unfold_3803_);
lean_inc(v_defEqPerm_3802_);
lean_inc(v_defEqTrans_3801_);
lean_inc(v_whnf_3800_);
lean_inc(v_synthInstance_3799_);
lean_inc(v_funInfo_3798_);
lean_inc(v_inferType_3797_);
lean_dec(v_cache_3789_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3818_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
lean_inc(v_a_3783_);
v___x_3807_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3797_, v_a_3777_, v_a_3783_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3807_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_funInfo_3798_);
lean_ctor_set(v_reuseFailAlloc_3817_, 2, v_synthInstance_3799_);
lean_ctor_set(v_reuseFailAlloc_3817_, 3, v_whnf_3800_);
lean_ctor_set(v_reuseFailAlloc_3817_, 4, v_defEqTrans_3801_);
lean_ctor_set(v_reuseFailAlloc_3817_, 5, v_defEqPerm_3802_);
lean_ctor_set(v_reuseFailAlloc_3817_, 6, v_unfold_3803_);
v___x_3809_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 1, v___x_3809_);
v___x_3811_ = v___x_3795_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_mctx_3790_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3816_, 2, v_zetaDeltaFVarIds_3791_);
lean_ctor_set(v_reuseFailAlloc_3816_, 3, v_postponed_3792_);
lean_ctor_set(v_reuseFailAlloc_3816_, 4, v_diag_3793_);
v___x_3811_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3812_ = lean_st_ref_put(v_a_3306_, v___x_3811_);
if (v_isShared_3787_ == 0)
{
v___x_3814_ = v___x_3786_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3783_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3777_);
return v___x_3782_;
}
}
else
{
lean_dec(v_a_3777_);
return v___x_3782_;
}
}
v___jp_3822_:
{
lean_object* v_toCold_3823_; lean_object* v_cancelTk_x3f_3824_; 
v_toCold_3823_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3824_ = lean_ctor_get(v_toCold_3823_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3824_) == 1)
{
lean_object* v_val_3825_; uint8_t v___x_3826_; 
v_val_3825_ = lean_ctor_get(v_cancelTk_x3f_3824_, 0);
v___x_3826_ = l_IO_CancelToken_isSet(v_val_3825_);
if (v___x_3826_ == 0)
{
goto v___jp_3781_;
}
else
{
lean_object* v___x_3827_; lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v_a_3777_);
lean_dec_ref(v_struct_3757_);
lean_dec(v_idx_3756_);
lean_dec(v_typeName_3755_);
v___x_3827_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
else
{
goto v___jp_3781_;
}
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec_ref(v_struct_3757_);
lean_dec(v_idx_3756_);
lean_dec(v_typeName_3755_);
v_a_3883_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3776_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3776_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3304_, 3);
goto v___jp_3758_;
}
}
v___jp_3758_:
{
lean_object* v_toCold_3759_; lean_object* v_cancelTk_x3f_3760_; 
v_toCold_3759_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3760_ = lean_ctor_get(v_toCold_3759_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3760_) == 1)
{
lean_object* v_val_3761_; uint8_t v___x_3762_; 
v_val_3761_ = lean_ctor_get(v_cancelTk_x3f_3760_, 0);
v___x_3762_ = l_IO_CancelToken_isSet(v_val_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; 
v___x_3763_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3755_, v_idx_3756_, v_struct_3757_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v_struct_3757_);
lean_dec(v_idx_3756_);
lean_dec(v_typeName_3755_);
v___x_3764_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v___x_3773_; 
v___x_3773_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3755_, v_idx_3756_, v_struct_3757_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3773_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3891_; 
v_cacheInferType_3891_ = lean_ctor_get_uint8(v_a_3305_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3891_ == 0)
{
goto v___jp_3326_;
}
else
{
uint8_t v___x_3892_; 
v___x_3892_ = l_Lean_Expr_hasMVar(v_e_3304_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; 
lean_inc_ref(v_e_3304_);
v___x_3893_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3304_, v_a_3305_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3999_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3999_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3999_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3953_; lean_object* v_cache_3954_; lean_object* v_inferType_3955_; lean_object* v___x_3956_; 
v___x_3953_ = lean_st_ref_get(v_a_3306_);
v_cache_3954_ = lean_ctor_get(v___x_3953_, 1);
lean_inc_ref(v_cache_3954_);
lean_dec(v___x_3953_);
v_inferType_3955_ = lean_ctor_get(v_cache_3954_, 0);
lean_inc_ref(v_inferType_3955_);
lean_dec_ref(v_cache_3954_);
v___x_3956_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3955_, v_a_3894_);
if (lean_obj_tag(v___x_3956_) == 1)
{
lean_object* v_val_3957_; lean_object* v_fst_3958_; lean_object* v_snd_3959_; lean_object* v_expr_3960_; uint64_t v_configKey_3961_; lean_object* v_expr_3962_; uint64_t v_configKey_3963_; uint8_t v___x_3964_; 
v_val_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_val_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v_fst_3958_ = lean_ctor_get(v_val_3957_, 0);
lean_inc(v_fst_3958_);
v_snd_3959_ = lean_ctor_get(v_val_3957_, 1);
lean_inc(v_snd_3959_);
lean_dec(v_val_3957_);
v_expr_3960_ = lean_ctor_get(v_a_3894_, 0);
v_configKey_3961_ = lean_ctor_get_uint64(v_a_3894_, sizeof(void*)*1);
v_expr_3962_ = lean_ctor_get(v_fst_3958_, 0);
lean_inc_ref(v_expr_3962_);
v_configKey_3963_ = lean_ctor_get_uint64(v_fst_3958_, sizeof(void*)*1);
lean_dec(v_fst_3958_);
v___x_3964_ = lean_uint64_dec_eq(v_configKey_3961_, v_configKey_3963_);
if (v___x_3964_ == 0)
{
lean_dec_ref(v_expr_3962_);
lean_dec(v_snd_3959_);
lean_dec_ref(v_inferType_3955_);
lean_del_object(v___x_3896_);
goto v___jp_3939_;
}
else
{
size_t v___x_3965_; uint8_t v___x_3966_; 
v___x_3965_ = ((size_t)64ULL);
v___x_3966_ = lean_expr_equal_budgeted(v_expr_3960_, v_expr_3962_, v___x_3965_);
lean_dec_ref(v_expr_3962_);
switch(v___x_3966_)
{
case 0:
{
lean_dec(v_snd_3959_);
lean_dec_ref(v_inferType_3955_);
lean_del_object(v___x_3896_);
goto v___jp_3939_;
}
case 1:
{
lean_object* v___x_3968_; 
lean_dec_ref(v_inferType_3955_);
lean_dec(v_a_3894_);
lean_dec_ref(v_e_3304_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v_snd_3959_);
v___x_3968_ = v___x_3896_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_snd_3959_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
default: 
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v_cache_3972_; lean_object* v_mctx_3973_; lean_object* v_zetaDeltaFVarIds_3974_; lean_object* v_postponed_3975_; lean_object* v_diag_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3998_; 
lean_dec(v_snd_3959_);
lean_del_object(v___x_3896_);
v___x_3970_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_inferType_3955_, v_a_3894_);
v___x_3971_ = lean_st_ref_take(v_a_3306_);
v_cache_3972_ = lean_ctor_get(v___x_3971_, 1);
v_mctx_3973_ = lean_ctor_get(v___x_3971_, 0);
v_zetaDeltaFVarIds_3974_ = lean_ctor_get(v___x_3971_, 2);
v_postponed_3975_ = lean_ctor_get(v___x_3971_, 3);
v_diag_3976_ = lean_ctor_get(v___x_3971_, 4);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3978_ = v___x_3971_;
v_isShared_3979_ = v_isSharedCheck_3998_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_diag_3976_);
lean_inc(v_postponed_3975_);
lean_inc(v_zetaDeltaFVarIds_3974_);
lean_inc(v_cache_3972_);
lean_inc(v_mctx_3973_);
lean_dec(v___x_3971_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3998_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_funInfo_3980_; lean_object* v_synthInstance_3981_; lean_object* v_whnf_3982_; lean_object* v_defEqTrans_3983_; lean_object* v_defEqPerm_3984_; lean_object* v_unfold_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3996_; 
v_funInfo_3980_ = lean_ctor_get(v_cache_3972_, 1);
v_synthInstance_3981_ = lean_ctor_get(v_cache_3972_, 2);
v_whnf_3982_ = lean_ctor_get(v_cache_3972_, 3);
v_defEqTrans_3983_ = lean_ctor_get(v_cache_3972_, 4);
v_defEqPerm_3984_ = lean_ctor_get(v_cache_3972_, 5);
v_unfold_3985_ = lean_ctor_get(v_cache_3972_, 6);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_cache_3972_);
if (v_isSharedCheck_3996_ == 0)
{
lean_object* v_unused_3997_; 
v_unused_3997_ = lean_ctor_get(v_cache_3972_, 0);
lean_dec(v_unused_3997_);
v___x_3987_ = v_cache_3972_;
v_isShared_3988_ = v_isSharedCheck_3996_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_unfold_3985_);
lean_inc(v_defEqPerm_3984_);
lean_inc(v_defEqTrans_3983_);
lean_inc(v_whnf_3982_);
lean_inc(v_synthInstance_3981_);
lean_inc(v_funInfo_3980_);
lean_dec(v_cache_3972_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3996_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3970_);
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_funInfo_3980_);
lean_ctor_set(v_reuseFailAlloc_3995_, 2, v_synthInstance_3981_);
lean_ctor_set(v_reuseFailAlloc_3995_, 3, v_whnf_3982_);
lean_ctor_set(v_reuseFailAlloc_3995_, 4, v_defEqTrans_3983_);
lean_ctor_set(v_reuseFailAlloc_3995_, 5, v_defEqPerm_3984_);
lean_ctor_set(v_reuseFailAlloc_3995_, 6, v_unfold_3985_);
v___x_3990_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3992_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_3990_);
v___x_3992_ = v___x_3978_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_mctx_3973_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3994_, 2, v_zetaDeltaFVarIds_3974_);
lean_ctor_set(v_reuseFailAlloc_3994_, 3, v_postponed_3975_);
lean_ctor_set(v_reuseFailAlloc_3994_, 4, v_diag_3976_);
v___x_3992_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_st_ref_put(v_a_3306_, v___x_3992_);
goto v___jp_3939_;
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
lean_dec(v___x_3956_);
lean_dec_ref(v_inferType_3955_);
lean_del_object(v___x_3896_);
goto v___jp_3939_;
}
v___jp_3898_:
{
lean_object* v___x_3899_; 
v___x_3899_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; uint8_t v___x_3901_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v___x_3901_ = l_Lean_Expr_hasMVar(v_a_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3937_; 
lean_inc(v_a_3900_);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v___x_3899_, 0);
lean_dec(v_unused_3938_);
v___x_3903_ = v___x_3899_;
v_isShared_3904_ = v_isSharedCheck_3937_;
goto v_resetjp_3902_;
}
else
{
lean_dec(v___x_3899_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3937_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v_cache_3906_; lean_object* v_mctx_3907_; lean_object* v_zetaDeltaFVarIds_3908_; lean_object* v_postponed_3909_; lean_object* v_diag_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3936_; 
v___x_3905_ = lean_st_ref_take(v_a_3306_);
v_cache_3906_ = lean_ctor_get(v___x_3905_, 1);
v_mctx_3907_ = lean_ctor_get(v___x_3905_, 0);
v_zetaDeltaFVarIds_3908_ = lean_ctor_get(v___x_3905_, 2);
v_postponed_3909_ = lean_ctor_get(v___x_3905_, 3);
v_diag_3910_ = lean_ctor_get(v___x_3905_, 4);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3912_ = v___x_3905_;
v_isShared_3913_ = v_isSharedCheck_3936_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_diag_3910_);
lean_inc(v_postponed_3909_);
lean_inc(v_zetaDeltaFVarIds_3908_);
lean_inc(v_cache_3906_);
lean_inc(v_mctx_3907_);
lean_dec(v___x_3905_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3936_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_inferType_3914_; lean_object* v_funInfo_3915_; lean_object* v_synthInstance_3916_; lean_object* v_whnf_3917_; lean_object* v_defEqTrans_3918_; lean_object* v_defEqPerm_3919_; lean_object* v_unfold_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3935_; 
v_inferType_3914_ = lean_ctor_get(v_cache_3906_, 0);
v_funInfo_3915_ = lean_ctor_get(v_cache_3906_, 1);
v_synthInstance_3916_ = lean_ctor_get(v_cache_3906_, 2);
v_whnf_3917_ = lean_ctor_get(v_cache_3906_, 3);
v_defEqTrans_3918_ = lean_ctor_get(v_cache_3906_, 4);
v_defEqPerm_3919_ = lean_ctor_get(v_cache_3906_, 5);
v_unfold_3920_ = lean_ctor_get(v_cache_3906_, 6);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_cache_3906_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3922_ = v_cache_3906_;
v_isShared_3923_ = v_isSharedCheck_3935_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_unfold_3920_);
lean_inc(v_defEqPerm_3919_);
lean_inc(v_defEqTrans_3918_);
lean_inc(v_whnf_3917_);
lean_inc(v_synthInstance_3916_);
lean_inc(v_funInfo_3915_);
lean_inc(v_inferType_3914_);
lean_dec(v_cache_3906_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3935_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_inc(v_a_3900_);
v___x_3924_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3914_, v_a_3894_, v_a_3900_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 0, v___x_3924_);
v___x_3926_ = v___x_3922_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_funInfo_3915_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_synthInstance_3916_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v_whnf_3917_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v_defEqTrans_3918_);
lean_ctor_set(v_reuseFailAlloc_3934_, 5, v_defEqPerm_3919_);
lean_ctor_set(v_reuseFailAlloc_3934_, 6, v_unfold_3920_);
v___x_3926_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
lean_object* v___x_3928_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 1, v___x_3926_);
v___x_3928_ = v___x_3912_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_mctx_3907_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3933_, 2, v_zetaDeltaFVarIds_3908_);
lean_ctor_set(v_reuseFailAlloc_3933_, 3, v_postponed_3909_);
lean_ctor_set(v_reuseFailAlloc_3933_, 4, v_diag_3910_);
v___x_3928_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = lean_st_ref_put(v_a_3306_, v___x_3928_);
if (v_isShared_3904_ == 0)
{
v___x_3931_ = v___x_3903_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3900_);
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
}
}
}
else
{
lean_dec(v_a_3894_);
return v___x_3899_;
}
}
else
{
lean_dec(v_a_3894_);
return v___x_3899_;
}
}
v___jp_3939_:
{
lean_object* v_toCold_3940_; lean_object* v_cancelTk_x3f_3941_; 
v_toCold_3940_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3941_ = lean_ctor_get(v_toCold_3940_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3941_) == 1)
{
lean_object* v_val_3942_; uint8_t v___x_3943_; 
v_val_3942_ = lean_ctor_get(v_cancelTk_x3f_3941_, 0);
v___x_3943_ = l_IO_CancelToken_isSet(v_val_3942_);
if (v___x_3943_ == 0)
{
goto v___jp_3898_;
}
else
{
lean_object* v___x_3944_; lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_a_3894_);
lean_dec_ref(v_e_3304_);
v___x_3944_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
goto v___jp_3898_;
}
}
}
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref(v_e_3304_);
v_a_4000_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3893_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3893_);
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
else
{
goto v___jp_3326_;
}
}
}
}
v___jp_3310_:
{
lean_object* v_toCold_3311_; lean_object* v_cancelTk_x3f_3312_; 
v_toCold_3311_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3312_ = lean_ctor_get(v_toCold_3311_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3312_) == 1)
{
lean_object* v_val_3313_; uint8_t v___x_3314_; 
v_val_3313_ = lean_ctor_get(v_cancelTk_x3f_3312_, 0);
v___x_3314_ = l_IO_CancelToken_isSet(v_val_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; 
v___x_3315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3315_;
}
else
{
lean_object* v___x_3316_; lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref(v_e_3304_);
v___x_3316_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v___x_3325_; 
v___x_3325_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3325_;
}
}
v___jp_3326_:
{
lean_object* v_toCold_3327_; lean_object* v_cancelTk_x3f_3328_; 
v_toCold_3327_ = lean_ctor_get(v_a_3307_, 0);
v_cancelTk_x3f_3328_ = lean_ctor_get(v_toCold_3327_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3328_) == 1)
{
lean_object* v_val_3329_; uint8_t v___x_3330_; 
v_val_3329_ = lean_ctor_get(v_cancelTk_x3f_3328_, 0);
v___x_3330_ = l_IO_CancelToken_isSet(v_val_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3331_;
}
else
{
lean_object* v___x_3332_; lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref(v_e_3304_);
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
v___x_3341_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_4015_, lean_object* v_x_4016_, lean_object* v_x_4017_, lean_object* v_x_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_4016_, v_x_4017_, v_x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_4020_, lean_object* v_x_4021_, lean_object* v_x_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_4021_, v_x_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_4024_, lean_object* v_x_4025_, lean_object* v_x_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_4024_, v_x_4025_, v_x_4026_);
lean_dec_ref(v_x_4026_);
lean_dec_ref(v_x_4025_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(lean_object* v_00_u03b2_4028_, lean_object* v_x_4029_, lean_object* v_x_4030_){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___redArg(v_x_4029_, v_x_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3___boxed(lean_object* v_00_u03b2_4032_, lean_object* v_x_4033_, lean_object* v_x_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3(v_00_u03b2_4032_, v_x_4033_, v_x_4034_);
lean_dec_ref(v_x_4034_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_4036_, lean_object* v_x_4037_, size_t v_x_4038_, size_t v_x_4039_, lean_object* v_x_4040_, lean_object* v_x_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_4037_, v_x_4038_, v_x_4039_, v_x_4040_, v_x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4043_, lean_object* v_x_4044_, lean_object* v_x_4045_, lean_object* v_x_4046_, lean_object* v_x_4047_, lean_object* v_x_4048_){
_start:
{
size_t v_x_5606__boxed_4049_; size_t v_x_5607__boxed_4050_; lean_object* v_res_4051_; 
v_x_5606__boxed_4049_ = lean_unbox_usize(v_x_4045_);
lean_dec(v_x_4045_);
v_x_5607__boxed_4050_ = lean_unbox_usize(v_x_4046_);
lean_dec(v_x_4046_);
v_res_4051_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_4043_, v_x_4044_, v_x_5606__boxed_4049_, v_x_5607__boxed_4050_, v_x_4047_, v_x_4048_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_4052_, lean_object* v_x_4053_, size_t v_x_4054_, lean_object* v_x_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_4053_, v_x_4054_, v_x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4057_, lean_object* v_x_4058_, lean_object* v_x_4059_, lean_object* v_x_4060_){
_start:
{
size_t v_x_5623__boxed_4061_; lean_object* v_res_4062_; 
v_x_5623__boxed_4061_ = lean_unbox_usize(v_x_4059_);
lean_dec(v_x_4059_);
v_res_4062_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_4057_, v_x_4058_, v_x_5623__boxed_4061_, v_x_4060_);
lean_dec_ref(v_x_4060_);
lean_dec_ref(v_x_4058_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(lean_object* v_00_u03b2_4063_, lean_object* v_x_4064_, size_t v_x_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___redArg(v_x_4064_, v_x_4065_, v_x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5___boxed(lean_object* v_00_u03b2_4068_, lean_object* v_x_4069_, lean_object* v_x_4070_, lean_object* v_x_4071_){
_start:
{
size_t v_x_5634__boxed_4072_; lean_object* v_res_4073_; 
v_x_5634__boxed_4072_ = lean_unbox_usize(v_x_4070_);
lean_dec(v_x_4070_);
v_res_4073_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__3_spec__5(v_00_u03b2_4068_, v_x_4069_, v_x_5634__boxed_4072_, v_x_4071_);
lean_dec_ref(v_x_4071_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_4074_, lean_object* v_n_4075_, lean_object* v_k_4076_, lean_object* v_v_4077_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_4075_, v_k_4076_, v_v_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_4079_, size_t v_depth_4080_, lean_object* v_keys_4081_, lean_object* v_vals_4082_, lean_object* v_heq_4083_, lean_object* v_i_4084_, lean_object* v_entries_4085_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_4080_, v_keys_4081_, v_vals_4082_, v_i_4084_, v_entries_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_4087_, lean_object* v_depth_4088_, lean_object* v_keys_4089_, lean_object* v_vals_4090_, lean_object* v_heq_4091_, lean_object* v_i_4092_, lean_object* v_entries_4093_){
_start:
{
size_t v_depth_boxed_4094_; lean_object* v_res_4095_; 
v_depth_boxed_4094_ = lean_unbox_usize(v_depth_4088_);
lean_dec(v_depth_4088_);
v_res_4095_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_4087_, v_depth_boxed_4094_, v_keys_4089_, v_vals_4090_, v_heq_4091_, v_i_4092_, v_entries_4093_);
lean_dec_ref(v_vals_4090_);
lean_dec_ref(v_keys_4089_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_4096_, lean_object* v_keys_4097_, lean_object* v_vals_4098_, lean_object* v_heq_4099_, lean_object* v_i_4100_, lean_object* v_k_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_4097_, v_vals_4098_, v_i_4100_, v_k_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4103_, lean_object* v_keys_4104_, lean_object* v_vals_4105_, lean_object* v_heq_4106_, lean_object* v_i_4107_, lean_object* v_k_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_4103_, v_keys_4104_, v_vals_4105_, v_heq_4106_, v_i_4107_, v_k_4108_);
lean_dec_ref(v_k_4108_);
lean_dec_ref(v_vals_4105_);
lean_dec_ref(v_keys_4104_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_4110_, lean_object* v_x_4111_, lean_object* v_x_4112_, lean_object* v_x_4113_, lean_object* v_x_4114_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__5___redArg(v_x_4111_, v_x_4112_, v_x_4113_, v_x_4114_);
return v___x_4115_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = l_Lean_maxRecDepthErrorMessage;
v___x_4122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_4124_ = l_Lean_MessageData_ofFormat(v___x_4123_);
return v___x_4124_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_4126_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_4127_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v___x_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_4128_){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4130_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4131_, 0, v_ref_4128_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4133_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_4136_, lean_object* v_ref_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4137_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_4144_, lean_object* v_ref_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_4144_, v_ref_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4205_; uint8_t v_beta_4206_; 
v___x_4205_ = l_Lean_Meta_Context_config(v___y_4153_);
v_beta_4206_ = lean_ctor_get_uint8(v___x_4205_, 13);
if (v_beta_4206_ == 0)
{
lean_dec_ref(v___x_4205_);
goto v___jp_4158_;
}
else
{
uint8_t v_iota_4207_; 
v_iota_4207_ = lean_ctor_get_uint8(v___x_4205_, 12);
if (v_iota_4207_ == 0)
{
lean_dec_ref(v___x_4205_);
goto v___jp_4158_;
}
else
{
uint8_t v_zeta_4208_; 
v_zeta_4208_ = lean_ctor_get_uint8(v___x_4205_, 15);
if (v_zeta_4208_ == 0)
{
lean_dec_ref(v___x_4205_);
goto v___jp_4158_;
}
else
{
uint8_t v_zetaHave_4209_; 
v_zetaHave_4209_ = lean_ctor_get_uint8(v___x_4205_, 18);
if (v_zetaHave_4209_ == 0)
{
lean_dec_ref(v___x_4205_);
goto v___jp_4158_;
}
else
{
uint8_t v_zetaDelta_4210_; 
v_zetaDelta_4210_ = lean_ctor_get_uint8(v___x_4205_, 16);
if (v_zetaDelta_4210_ == 0)
{
lean_dec_ref(v___x_4205_);
goto v___jp_4158_;
}
else
{
uint8_t v_etaStruct_4211_; uint8_t v_proj_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; 
v_etaStruct_4211_ = lean_ctor_get_uint8(v___x_4205_, 10);
v_proj_4212_ = lean_ctor_get_uint8(v___x_4205_, 14);
lean_dec_ref(v___x_4205_);
v___x_4213_ = lean_box(v_proj_4212_);
v___x_4214_ = lean_obj_tag_nat(v___x_4213_);
lean_dec(v___x_4213_);
v___x_4215_ = lean_unsigned_to_nat(2u);
v___x_4216_ = lean_nat_dec_eq(v___x_4214_, v___x_4215_);
if (v___x_4216_ == 0)
{
goto v___jp_4158_;
}
else
{
uint8_t v___x_4217_; uint8_t v___x_4218_; 
v___x_4217_ = 0;
v___x_4218_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4211_, v___x_4217_);
if (v___x_4218_ == 0)
{
goto v___jp_4158_;
}
else
{
lean_object* v___x_4219_; 
v___x_4219_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec_ref(v___y_4153_);
return v___x_4219_;
}
}
}
}
}
}
}
v___jp_4158_:
{
lean_object* v___x_4159_; uint8_t v_foApprox_4160_; uint8_t v_ctxApprox_4161_; uint8_t v_quasiPatternApprox_4162_; uint8_t v_constApprox_4163_; uint8_t v_isDefEqStuckEx_4164_; uint8_t v_unificationHints_4165_; uint8_t v_proofIrrelevance_4166_; uint8_t v_assignSyntheticOpaque_4167_; uint8_t v_offsetCnstrs_4168_; uint8_t v_transparency_4169_; uint8_t v_univApprox_4170_; uint8_t v_zetaUnused_4171_; uint8_t v_canUnfoldPredicateConfig_4172_; uint8_t v_stringLitToCtor_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4204_; 
v___x_4159_ = l_Lean_Meta_Context_config(v___y_4153_);
v_foApprox_4160_ = lean_ctor_get_uint8(v___x_4159_, 0);
v_ctxApprox_4161_ = lean_ctor_get_uint8(v___x_4159_, 1);
v_quasiPatternApprox_4162_ = lean_ctor_get_uint8(v___x_4159_, 2);
v_constApprox_4163_ = lean_ctor_get_uint8(v___x_4159_, 3);
v_isDefEqStuckEx_4164_ = lean_ctor_get_uint8(v___x_4159_, 4);
v_unificationHints_4165_ = lean_ctor_get_uint8(v___x_4159_, 5);
v_proofIrrelevance_4166_ = lean_ctor_get_uint8(v___x_4159_, 6);
v_assignSyntheticOpaque_4167_ = lean_ctor_get_uint8(v___x_4159_, 7);
v_offsetCnstrs_4168_ = lean_ctor_get_uint8(v___x_4159_, 8);
v_transparency_4169_ = lean_ctor_get_uint8(v___x_4159_, 9);
v_univApprox_4170_ = lean_ctor_get_uint8(v___x_4159_, 11);
v_zetaUnused_4171_ = lean_ctor_get_uint8(v___x_4159_, 17);
v_canUnfoldPredicateConfig_4172_ = lean_ctor_get_uint8(v___x_4159_, 19);
v_stringLitToCtor_4173_ = lean_ctor_get_uint8(v___x_4159_, 20);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4175_ = v___x_4159_;
v_isShared_4176_ = v_isSharedCheck_4204_;
goto v_resetjp_4174_;
}
else
{
lean_dec(v___x_4159_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4204_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
uint8_t v___x_4177_; uint8_t v___x_4178_; uint8_t v___x_4179_; lean_object* v___x_4181_; 
v___x_4177_ = 1;
v___x_4178_ = 0;
v___x_4179_ = 2;
if (v_isShared_4176_ == 0)
{
v___x_4181_ = v___x_4175_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 0, 21);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 0, v_foApprox_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 1, v_ctxApprox_4161_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 2, v_quasiPatternApprox_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 3, v_constApprox_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 4, v_isDefEqStuckEx_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 5, v_unificationHints_4165_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 6, v_proofIrrelevance_4166_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 7, v_assignSyntheticOpaque_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 8, v_offsetCnstrs_4168_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 9, v_transparency_4169_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 11, v_univApprox_4170_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 17, v_zetaUnused_4171_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 19, v_canUnfoldPredicateConfig_4172_);
lean_ctor_set_uint8(v_reuseFailAlloc_4203_, 20, v_stringLitToCtor_4173_);
v___x_4181_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
uint8_t v_trackZetaDelta_4182_; lean_object* v_zetaDeltaSet_4183_; lean_object* v_lctx_4184_; lean_object* v_localInstances_4185_; lean_object* v_defEqCtx_x3f_4186_; lean_object* v_synthPendingDepth_4187_; lean_object* v_customCanUnfoldPredicate_x3f_4188_; uint8_t v_univApprox_4189_; uint8_t v_inTypeClassResolution_4190_; uint8_t v_cacheInferType_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4201_; 
lean_ctor_set_uint8(v___x_4181_, 10, v___x_4178_);
lean_ctor_set_uint8(v___x_4181_, 12, v___x_4177_);
lean_ctor_set_uint8(v___x_4181_, 13, v___x_4177_);
lean_ctor_set_uint8(v___x_4181_, 14, v___x_4179_);
lean_ctor_set_uint8(v___x_4181_, 15, v___x_4177_);
lean_ctor_set_uint8(v___x_4181_, 16, v___x_4177_);
lean_ctor_set_uint8(v___x_4181_, 18, v___x_4177_);
v_trackZetaDelta_4182_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*7);
v_zetaDeltaSet_4183_ = lean_ctor_get(v___y_4153_, 1);
v_lctx_4184_ = lean_ctor_get(v___y_4153_, 2);
v_localInstances_4185_ = lean_ctor_get(v___y_4153_, 3);
v_defEqCtx_x3f_4186_ = lean_ctor_get(v___y_4153_, 4);
v_synthPendingDepth_4187_ = lean_ctor_get(v___y_4153_, 5);
v_customCanUnfoldPredicate_x3f_4188_ = lean_ctor_get(v___y_4153_, 6);
v_univApprox_4189_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4190_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*7 + 2);
v_cacheInferType_4191_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*7 + 3);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___y_4153_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; 
v_unused_4202_ = lean_ctor_get(v___y_4153_, 0);
lean_dec(v_unused_4202_);
v___x_4193_ = v___y_4153_;
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4188_);
lean_inc(v_synthPendingDepth_4187_);
lean_inc(v_defEqCtx_x3f_4186_);
lean_inc(v_localInstances_4185_);
lean_inc(v_lctx_4184_);
lean_inc(v_zetaDeltaSet_4183_);
lean_dec(v___y_4153_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4201_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
uint64_t v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4181_);
v___x_4196_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4196_, 0, v___x_4181_);
lean_ctor_set_uint64(v___x_4196_, sizeof(void*)*1, v___x_4195_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v___x_4196_);
v___x_4198_ = v___x_4193_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_zetaDeltaSet_4183_);
lean_ctor_set(v_reuseFailAlloc_4200_, 2, v_lctx_4184_);
lean_ctor_set(v_reuseFailAlloc_4200_, 3, v_localInstances_4185_);
lean_ctor_set(v_reuseFailAlloc_4200_, 4, v_defEqCtx_x3f_4186_);
lean_ctor_set(v_reuseFailAlloc_4200_, 5, v_synthPendingDepth_4187_);
lean_ctor_set(v_reuseFailAlloc_4200_, 6, v_customCanUnfoldPredicate_x3f_4188_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*7, v_trackZetaDelta_4182_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*7 + 1, v_univApprox_4189_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4190_);
lean_ctor_set_uint8(v_reuseFailAlloc_4200_, sizeof(void*)*7 + 3, v_cacheInferType_4191_);
v___x_4198_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_4152_, v___x_4198_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec_ref(v___x_4198_);
return v___x_4199_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_){
_start:
{
lean_object* v___y_4234_; lean_object* v_toCold_4251_; lean_object* v_currRecDepth_4252_; lean_object* v_ref_4253_; uint16_t v_optionFlags_4254_; uint8_t v_suppressElabErrors_4255_; uint8_t v_checkDeprecated_4256_; uint8_t v_isRecordingDeps_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4297_; 
v_toCold_4251_ = lean_ctor_get(v_a_4230_, 0);
v_currRecDepth_4252_ = lean_ctor_get(v_a_4230_, 1);
v_ref_4253_ = lean_ctor_get(v_a_4230_, 2);
v_optionFlags_4254_ = lean_ctor_get_uint16(v_a_4230_, sizeof(void*)*3);
v_suppressElabErrors_4255_ = lean_ctor_get_uint8(v_a_4230_, sizeof(void*)*3 + 2);
v_checkDeprecated_4256_ = lean_ctor_get_uint8(v_a_4230_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4257_ = lean_ctor_get_uint8(v_a_4230_, sizeof(void*)*3 + 4);
v_isSharedCheck_4297_ = !lean_is_exclusive(v_a_4230_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4259_ = v_a_4230_;
v_isShared_4260_ = v_isSharedCheck_4297_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_ref_4253_);
lean_inc(v_currRecDepth_4252_);
lean_inc(v_toCold_4251_);
lean_dec(v_a_4230_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4297_;
goto v_resetjp_4258_;
}
v___jp_4233_:
{
if (lean_obj_tag(v___y_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
v_a_4235_ = lean_ctor_get(v___y_4234_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___y_4234_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___y_4234_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___y_4234_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
v_a_4243_ = lean_ctor_get(v___y_4234_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___y_4234_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___y_4234_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___y_4234_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
v_resetjp_4258_:
{
lean_object* v_maxRecDepth_4261_; lean_object* v___x_4293_; uint8_t v___x_4294_; 
v_maxRecDepth_4261_ = lean_ctor_get(v_toCold_4251_, 3);
v___x_4293_ = lean_unsigned_to_nat(0u);
v___x_4294_ = lean_nat_dec_eq(v_maxRecDepth_4261_, v___x_4293_);
if (v___x_4294_ == 0)
{
uint8_t v___x_4295_; 
v___x_4295_ = lean_nat_dec_eq(v_currRecDepth_4252_, v_maxRecDepth_4261_);
if (v___x_4295_ == 0)
{
goto v___jp_4262_;
}
else
{
lean_object* v___x_4296_; 
lean_del_object(v___x_4259_);
lean_dec(v_currRecDepth_4252_);
lean_dec_ref(v_toCold_4251_);
lean_dec(v_a_4231_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
lean_dec_ref(v_e_4227_);
v___x_4296_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_4253_);
return v___x_4296_;
}
}
else
{
goto v___jp_4262_;
}
v___jp_4262_:
{
lean_object* v___x_4263_; uint8_t v_transparency_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4263_ = l_Lean_Meta_Context_config(v_a_4228_);
v_transparency_4264_ = lean_ctor_get_uint8(v___x_4263_, 9);
lean_dec_ref(v___x_4263_);
v___x_4265_ = lean_unsigned_to_nat(1u);
v___x_4266_ = lean_nat_add(v_currRecDepth_4252_, v___x_4265_);
lean_dec(v_currRecDepth_4252_);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 1, v___x_4266_);
v___x_4268_ = v___x_4259_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_toCold_4251_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4292_, 2, v_ref_4253_);
lean_ctor_set_uint16(v_reuseFailAlloc_4292_, sizeof(void*)*3, v_optionFlags_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4292_, sizeof(void*)*3 + 2, v_suppressElabErrors_4255_);
lean_ctor_set_uint8(v_reuseFailAlloc_4292_, sizeof(void*)*3 + 3, v_checkDeprecated_4256_);
lean_ctor_set_uint8(v_reuseFailAlloc_4292_, sizeof(void*)*3 + 4, v_isRecordingDeps_4257_);
v___x_4268_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
uint8_t v___x_4269_; uint8_t v___x_4270_; 
v___x_4269_ = 1;
v___x_4270_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4264_, v___x_4269_);
if (v___x_4270_ == 0)
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4227_, v_a_4228_, v_a_4229_, v___x_4268_, v_a_4231_);
lean_dec(v_a_4231_);
lean_dec_ref(v___x_4268_);
lean_dec(v_a_4229_);
v___y_4234_ = v___x_4271_;
goto v___jp_4233_;
}
else
{
lean_object* v_keyedConfig_4272_; uint8_t v_trackZetaDelta_4273_; lean_object* v_zetaDeltaSet_4274_; lean_object* v_lctx_4275_; lean_object* v_localInstances_4276_; lean_object* v_defEqCtx_x3f_4277_; lean_object* v_synthPendingDepth_4278_; lean_object* v_customCanUnfoldPredicate_x3f_4279_; uint8_t v_univApprox_4280_; uint8_t v_inTypeClassResolution_4281_; uint8_t v_cacheInferType_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4291_; 
v_keyedConfig_4272_ = lean_ctor_get(v_a_4228_, 0);
v_trackZetaDelta_4273_ = lean_ctor_get_uint8(v_a_4228_, sizeof(void*)*7);
v_zetaDeltaSet_4274_ = lean_ctor_get(v_a_4228_, 1);
v_lctx_4275_ = lean_ctor_get(v_a_4228_, 2);
v_localInstances_4276_ = lean_ctor_get(v_a_4228_, 3);
v_defEqCtx_x3f_4277_ = lean_ctor_get(v_a_4228_, 4);
v_synthPendingDepth_4278_ = lean_ctor_get(v_a_4228_, 5);
v_customCanUnfoldPredicate_x3f_4279_ = lean_ctor_get(v_a_4228_, 6);
v_univApprox_4280_ = lean_ctor_get_uint8(v_a_4228_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4281_ = lean_ctor_get_uint8(v_a_4228_, sizeof(void*)*7 + 2);
v_cacheInferType_4282_ = lean_ctor_get_uint8(v_a_4228_, sizeof(void*)*7 + 3);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_a_4228_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4284_ = v_a_4228_;
v_isShared_4285_ = v_isSharedCheck_4291_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4279_);
lean_inc(v_synthPendingDepth_4278_);
lean_inc(v_defEqCtx_x3f_4277_);
lean_inc(v_localInstances_4276_);
lean_inc(v_lctx_4275_);
lean_inc(v_zetaDeltaSet_4274_);
lean_inc(v_keyedConfig_4272_);
lean_dec(v_a_4228_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4291_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4286_; lean_object* v___x_4288_; 
v___x_4286_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4269_, v_keyedConfig_4272_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 0, v___x_4286_);
v___x_4288_ = v___x_4284_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4286_);
lean_ctor_set(v_reuseFailAlloc_4290_, 1, v_zetaDeltaSet_4274_);
lean_ctor_set(v_reuseFailAlloc_4290_, 2, v_lctx_4275_);
lean_ctor_set(v_reuseFailAlloc_4290_, 3, v_localInstances_4276_);
lean_ctor_set(v_reuseFailAlloc_4290_, 4, v_defEqCtx_x3f_4277_);
lean_ctor_set(v_reuseFailAlloc_4290_, 5, v_synthPendingDepth_4278_);
lean_ctor_set(v_reuseFailAlloc_4290_, 6, v_customCanUnfoldPredicate_x3f_4279_);
lean_ctor_set_uint8(v_reuseFailAlloc_4290_, sizeof(void*)*7, v_trackZetaDelta_4273_);
lean_ctor_set_uint8(v_reuseFailAlloc_4290_, sizeof(void*)*7 + 1, v_univApprox_4280_);
lean_ctor_set_uint8(v_reuseFailAlloc_4290_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4281_);
lean_ctor_set_uint8(v_reuseFailAlloc_4290_, sizeof(void*)*7 + 3, v_cacheInferType_4282_);
v___x_4288_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_4227_, v___x_4288_, v_a_4229_, v___x_4268_, v_a_4231_);
lean_dec(v_a_4231_);
lean_dec_ref(v___x_4268_);
lean_dec(v_a_4229_);
v___y_4234_ = v___x_4289_;
goto v___jp_4233_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = lean_infer_type(v_e_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
return v_res_4304_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_4305_){
_start:
{
switch(lean_obj_tag(v_x_4305_))
{
case 0:
{
uint8_t v___x_4306_; 
v___x_4306_ = 1;
return v___x_4306_;
}
case 2:
{
lean_object* v_a_4307_; lean_object* v_a_4308_; uint8_t v___x_4309_; 
v_a_4307_ = lean_ctor_get(v_x_4305_, 0);
v_a_4308_ = lean_ctor_get(v_x_4305_, 1);
v___x_4309_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4307_);
if (v___x_4309_ == 0)
{
return v___x_4309_;
}
else
{
v_x_4305_ = v_a_4308_;
goto _start;
}
}
case 3:
{
lean_object* v_a_4311_; 
v_a_4311_ = lean_ctor_get(v_x_4305_, 1);
v_x_4305_ = v_a_4311_;
goto _start;
}
default: 
{
uint8_t v___x_4313_; 
v___x_4313_ = 0;
return v___x_4313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_4314_){
_start:
{
uint8_t v_res_4315_; lean_object* v_r_4316_; 
v_res_4315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_4314_);
lean_dec(v_x_4314_);
v_r_4316_ = lean_box(v_res_4315_);
return v_r_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; lean_object* v_mctx_4321_; lean_object* v___x_4322_; lean_object* v_fst_4323_; lean_object* v_snd_4324_; lean_object* v___x_4325_; lean_object* v_cache_4326_; lean_object* v_zetaDeltaFVarIds_4327_; lean_object* v_postponed_4328_; lean_object* v_diag_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4338_; 
v___x_4320_ = lean_st_ref_get(v___y_4318_);
v_mctx_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc_ref(v_mctx_4321_);
lean_dec(v___x_4320_);
v___x_4322_ = lean_instantiate_level_mvars(v_mctx_4321_, v_l_4317_);
v_fst_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_fst_4323_);
v_snd_4324_ = lean_ctor_get(v___x_4322_, 1);
lean_inc(v_snd_4324_);
lean_dec_ref(v___x_4322_);
v___x_4325_ = lean_st_ref_take(v___y_4318_);
v_cache_4326_ = lean_ctor_get(v___x_4325_, 1);
v_zetaDeltaFVarIds_4327_ = lean_ctor_get(v___x_4325_, 2);
v_postponed_4328_ = lean_ctor_get(v___x_4325_, 3);
v_diag_4329_ = lean_ctor_get(v___x_4325_, 4);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4338_ == 0)
{
lean_object* v_unused_4339_; 
v_unused_4339_ = lean_ctor_get(v___x_4325_, 0);
lean_dec(v_unused_4339_);
v___x_4331_ = v___x_4325_;
v_isShared_4332_ = v_isSharedCheck_4338_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_diag_4329_);
lean_inc(v_postponed_4328_);
lean_inc(v_zetaDeltaFVarIds_4327_);
lean_inc(v_cache_4326_);
lean_dec(v___x_4325_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4338_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 0, v_fst_4323_);
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_fst_4323_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v_cache_4326_);
lean_ctor_set(v_reuseFailAlloc_4337_, 2, v_zetaDeltaFVarIds_4327_);
lean_ctor_set(v_reuseFailAlloc_4337_, 3, v_postponed_4328_);
lean_ctor_set(v_reuseFailAlloc_4337_, 4, v_diag_4329_);
v___x_4334_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_st_ref_put(v___y_4318_, v___x_4334_);
v___x_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4336_, 0, v_snd_4324_);
return v___x_4336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4340_, v___y_4341_);
lean_dec(v___y_4341_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_4344_, v___y_4346_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_00_u03c3_4358_, lean_object* v_x_4359_, lean_object* v_x_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v___y_4371_; 
switch(lean_obj_tag(v_x_4359_))
{
case 3:
{
lean_object* v_u_4392_; lean_object* v___x_4393_; uint8_t v___x_4394_; 
v_u_4392_ = lean_ctor_get(v_x_4359_, 0);
lean_inc(v_u_4392_);
lean_dec_ref_known(v_x_4359_, 1);
v___x_4393_ = lean_unsigned_to_nat(0u);
v___x_4394_ = lean_nat_dec_eq(v_x_4360_, v___x_4393_);
lean_dec(v_x_4360_);
if (v___x_4394_ == 0)
{
lean_dec(v_u_4392_);
lean_dec_ref(v_00_u03c3_4358_);
goto v___jp_4366_;
}
else
{
lean_object* v_paramNames_4395_; lean_object* v_lvls_4396_; uint8_t v___x_4397_; 
v_paramNames_4395_ = lean_ctor_get(v_00_u03c3_4358_, 0);
lean_inc(v_paramNames_4395_);
v_lvls_4396_ = lean_ctor_get(v_00_u03c3_4358_, 1);
lean_inc(v_lvls_4396_);
lean_dec_ref(v_00_u03c3_4358_);
v___x_4397_ = l_List_isEmpty___redArg(v_paramNames_4395_);
if (v___x_4397_ == 0)
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_Level_instantiateParams(v_u_4392_, v_paramNames_4395_, v_lvls_4396_);
v___y_4371_ = v___x_4398_;
goto v___jp_4370_;
}
else
{
lean_dec(v_lvls_4396_);
lean_dec(v_paramNames_4395_);
v___y_4371_ = v_u_4392_;
goto v___jp_4370_;
}
}
}
case 7:
{
lean_object* v_body_4399_; lean_object* v_zero_4400_; uint8_t v_isZero_4401_; 
v_body_4399_ = lean_ctor_get(v_x_4359_, 2);
lean_inc_ref(v_body_4399_);
lean_dec_ref_known(v_x_4359_, 3);
v_zero_4400_ = lean_unsigned_to_nat(0u);
v_isZero_4401_ = lean_nat_dec_eq(v_x_4360_, v_zero_4400_);
if (v_isZero_4401_ == 1)
{
uint8_t v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
lean_dec_ref(v_body_4399_);
lean_dec(v_x_4360_);
lean_dec_ref(v_00_u03c3_4358_);
v___x_4402_ = 0;
v___x_4403_ = lean_box(v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
else
{
lean_object* v_one_4405_; lean_object* v_n_4406_; 
v_one_4405_ = lean_unsigned_to_nat(1u);
v_n_4406_ = lean_nat_sub(v_x_4360_, v_one_4405_);
lean_dec(v_x_4360_);
v_x_4359_ = v_body_4399_;
v_x_4360_ = v_n_4406_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4408_; 
v_body_4408_ = lean_ctor_get(v_x_4359_, 3);
lean_inc_ref(v_body_4408_);
lean_dec_ref_known(v_x_4359_, 4);
v_x_4359_ = v_body_4408_;
goto _start;
}
case 10:
{
lean_object* v_expr_4410_; 
v_expr_4410_ = lean_ctor_get(v_x_4359_, 1);
lean_inc_ref(v_expr_4410_);
lean_dec_ref_known(v_x_4359_, 2);
v_x_4359_ = v_expr_4410_;
goto _start;
}
default: 
{
lean_dec(v_x_4360_);
lean_dec_ref(v_x_4359_);
lean_dec_ref(v_00_u03c3_4358_);
goto v___jp_4366_;
}
}
v___jp_4366_:
{
uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4367_ = 2;
v___x_4368_ = lean_box(v___x_4367_);
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
return v___x_4369_;
}
v___jp_4370_:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v___y_4371_, v_a_4362_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4383_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4375_ = v___x_4372_;
v_isShared_4376_ = v_isSharedCheck_4383_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4383_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
uint8_t v___x_4377_; uint8_t v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4377_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4373_);
lean_dec(v_a_4373_);
v___x_4378_ = l_Lean_Bool_toLBool(v___x_4377_);
v___x_4379_ = lean_box(v___x_4378_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4379_);
v___x_4381_ = v___x_4375_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
v_a_4384_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4372_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4372_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_00_u03c3_4412_, lean_object* v_x_4413_, lean_object* v_x_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_00_u03c3_4412_, v_x_4413_, v_x_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
lean_dec(v_a_4418_);
lean_dec_ref(v_a_4417_);
lean_dec(v_a_4416_);
lean_dec_ref(v_a_4415_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(lean_object* v_00_u03c3_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
if (lean_obj_tag(v_a_4422_) == 0)
{
lean_object* v___x_4424_; 
lean_dec_ref(v_00_u03c3_4421_);
v___x_4424_ = l_List_reverse___redArg(v_a_4423_);
return v___x_4424_;
}
else
{
lean_object* v_head_4425_; lean_object* v_tail_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4440_; 
v_head_4425_ = lean_ctor_get(v_a_4422_, 0);
v_tail_4426_ = lean_ctor_get(v_a_4422_, 1);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_a_4422_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4428_ = v_a_4422_;
v_isShared_4429_ = v_isSharedCheck_4440_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_tail_4426_);
lean_inc(v_head_4425_);
lean_dec(v_a_4422_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4440_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___y_4431_; lean_object* v_paramNames_4436_; lean_object* v_lvls_4437_; uint8_t v___x_4438_; 
v_paramNames_4436_ = lean_ctor_get(v_00_u03c3_4421_, 0);
v_lvls_4437_ = lean_ctor_get(v_00_u03c3_4421_, 1);
v___x_4438_ = l_List_isEmpty___redArg(v_paramNames_4436_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; 
lean_inc(v_lvls_4437_);
lean_inc(v_paramNames_4436_);
v___x_4439_ = l_Lean_Level_instantiateParams(v_head_4425_, v_paramNames_4436_, v_lvls_4437_);
v___y_4431_ = v___x_4439_;
goto v___jp_4430_;
}
else
{
v___y_4431_ = v_head_4425_;
goto v___jp_4430_;
}
v___jp_4430_:
{
lean_object* v___x_4433_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 1, v_a_4423_);
lean_ctor_set(v___x_4428_, 0, v___y_4431_);
v___x_4433_ = v___x_4428_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___y_4431_);
lean_ctor_set(v_reuseFailAlloc_4435_, 1, v_a_4423_);
v___x_4433_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
v_a_4422_ = v_tail_4426_;
v_a_4423_ = v___x_4433_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_00_u03c3_4443_, lean_object* v_x_4444_, lean_object* v_x_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
switch(lean_obj_tag(v_x_4444_))
{
case 4:
{
lean_object* v_declName_4451_; lean_object* v_us_4452_; lean_object* v___y_4454_; lean_object* v_paramNames_4468_; uint8_t v___x_4469_; 
v_declName_4451_ = lean_ctor_get(v_x_4444_, 0);
lean_inc(v_declName_4451_);
v_us_4452_ = lean_ctor_get(v_x_4444_, 1);
lean_inc(v_us_4452_);
lean_dec_ref_known(v_x_4444_, 2);
v_paramNames_4468_ = lean_ctor_get(v_00_u03c3_4443_, 0);
v___x_4469_ = l_List_isEmpty___redArg(v_paramNames_4468_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = lean_box(0);
v___x_4471_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4443_, v_us_4452_, v___x_4470_);
v___y_4454_ = v___x_4471_;
goto v___jp_4453_;
}
else
{
lean_dec_ref(v_00_u03c3_4443_);
v___y_4454_ = v_us_4452_;
goto v___jp_4453_;
}
v___jp_4453_:
{
lean_object* v___x_4455_; 
v___x_4455_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4451_, v___y_4454_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v_fst_4457_; lean_object* v_snd_4458_; lean_object* v___x_4459_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v_fst_4457_ = lean_ctor_get(v_a_4456_, 0);
lean_inc(v_fst_4457_);
v_snd_4458_ = lean_ctor_get(v_a_4456_, 1);
lean_inc(v_snd_4458_);
lean_dec(v_a_4456_);
v___x_4459_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4458_, v_fst_4457_, v_x_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
return v___x_4459_;
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec(v_x_4445_);
v_a_4460_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4455_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4455_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_4472_; lean_object* v___x_4473_; 
lean_dec_ref(v_00_u03c3_4443_);
v_fvarId_4472_ = lean_ctor_get(v_x_4444_, 0);
lean_inc(v_fvarId_4472_);
lean_dec_ref_known(v_x_4444_, 1);
v___x_4473_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4472_, v_a_4446_, v_a_4448_, v_a_4449_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4476_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4475_, v_a_4474_, v_x_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
return v___x_4476_;
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec(v_x_4445_);
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
case 2:
{
lean_object* v_mvarId_4485_; lean_object* v___x_4486_; 
lean_dec_ref(v_00_u03c3_4443_);
v_mvarId_4485_ = lean_ctor_get(v_x_4444_, 0);
lean_inc(v_mvarId_4485_);
lean_dec_ref_known(v_x_4444_, 1);
v___x_4486_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4485_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___x_4488_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4488_, v_a_4487_, v_x_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
return v___x_4489_;
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec(v_x_4445_);
v_a_4490_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4486_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4486_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
case 5:
{
lean_object* v_fn_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v_fn_4498_ = lean_ctor_get(v_x_4444_, 0);
lean_inc_ref(v_fn_4498_);
lean_dec_ref_known(v_x_4444_, 2);
v___x_4499_ = lean_unsigned_to_nat(1u);
v___x_4500_ = lean_nat_add(v_x_4445_, v___x_4499_);
lean_dec(v_x_4445_);
v_x_4444_ = v_fn_4498_;
v_x_4445_ = v___x_4500_;
goto _start;
}
case 10:
{
lean_object* v_expr_4502_; 
v_expr_4502_ = lean_ctor_get(v_x_4444_, 1);
lean_inc_ref(v_expr_4502_);
lean_dec_ref_known(v_x_4444_, 2);
v_x_4444_ = v_expr_4502_;
goto _start;
}
case 8:
{
lean_object* v_body_4504_; 
v_body_4504_ = lean_ctor_get(v_x_4444_, 3);
lean_inc_ref(v_body_4504_);
lean_dec_ref_known(v_x_4444_, 4);
v_x_4444_ = v_body_4504_;
goto _start;
}
case 6:
{
lean_object* v_body_4506_; lean_object* v_zero_4507_; uint8_t v_isZero_4508_; 
v_body_4506_ = lean_ctor_get(v_x_4444_, 2);
lean_inc_ref(v_body_4506_);
lean_dec_ref_known(v_x_4444_, 3);
v_zero_4507_ = lean_unsigned_to_nat(0u);
v_isZero_4508_ = lean_nat_dec_eq(v_x_4445_, v_zero_4507_);
if (v_isZero_4508_ == 1)
{
uint8_t v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec_ref(v_body_4506_);
lean_dec(v_x_4445_);
lean_dec_ref(v_00_u03c3_4443_);
v___x_4509_ = 0;
v___x_4510_ = lean_box(v___x_4509_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
return v___x_4511_;
}
else
{
lean_object* v_one_4512_; lean_object* v_n_4513_; 
v_one_4512_ = lean_unsigned_to_nat(1u);
v_n_4513_ = lean_nat_sub(v_x_4445_, v_one_4512_);
lean_dec(v_x_4445_);
v_x_4444_ = v_body_4506_;
v_x_4445_ = v_n_4513_;
goto _start;
}
}
default: 
{
uint8_t v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
lean_dec(v_x_4445_);
lean_dec_ref(v_x_4444_);
lean_dec_ref(v_00_u03c3_4443_);
v___x_4515_ = 2;
v___x_4516_ = lean_box(v___x_4515_);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_00_u03c3_4518_, lean_object* v_x_4519_, lean_object* v_x_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4518_, v_x_4519_, v_x_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(lean_object* v_00_u03c3_4527_, lean_object* v_x_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
switch(lean_obj_tag(v_x_4528_))
{
case 1:
{
lean_object* v_fvarId_4534_; lean_object* v___x_4535_; 
lean_dec_ref(v_00_u03c3_4527_);
v_fvarId_4534_ = lean_ctor_get(v_x_4528_, 0);
lean_inc(v_fvarId_4534_);
lean_dec_ref_known(v_x_4528_, 1);
v___x_4535_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4534_, v_a_4529_, v_a_4531_, v_a_4532_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v___x_4537_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4538_ = lean_unsigned_to_nat(0u);
v___x_4539_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4537_, v_a_4536_, v___x_4538_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
return v___x_4539_;
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
v_a_4540_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4535_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4535_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4548_; lean_object* v___x_4549_; 
lean_dec_ref(v_00_u03c3_4527_);
v_mvarId_4548_ = lean_ctor_get(v_x_4528_, 0);
lean_inc(v_mvarId_4548_);
lean_dec_ref_known(v_x_4528_, 1);
v___x_4549_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4548_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v___x_4551_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4552_ = lean_unsigned_to_nat(0u);
v___x_4553_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v___x_4551_, v_a_4550_, v___x_4552_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
return v___x_4553_;
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
v_a_4554_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4549_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4549_);
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
case 3:
{
uint8_t v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
lean_dec_ref_known(v_x_4528_, 1);
lean_dec_ref(v_00_u03c3_4527_);
v___x_4562_ = 0;
v___x_4563_ = lean_box(v___x_4562_);
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
return v___x_4564_;
}
case 4:
{
lean_object* v_declName_4565_; lean_object* v_us_4566_; lean_object* v___y_4568_; lean_object* v_paramNames_4583_; uint8_t v___x_4584_; 
v_declName_4565_ = lean_ctor_get(v_x_4528_, 0);
lean_inc(v_declName_4565_);
v_us_4566_ = lean_ctor_get(v_x_4528_, 1);
lean_inc(v_us_4566_);
lean_dec_ref_known(v_x_4528_, 2);
v_paramNames_4583_ = lean_ctor_get(v_00_u03c3_4527_, 0);
v___x_4584_ = l_List_isEmpty___redArg(v_paramNames_4583_);
if (v___x_4584_ == 0)
{
lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4585_ = lean_box(0);
v___x_4586_ = l_List_mapTR_loop___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_spec__0(v_00_u03c3_4527_, v_us_4566_, v___x_4585_);
v___y_4568_ = v___x_4586_;
goto v___jp_4567_;
}
else
{
lean_dec_ref(v_00_u03c3_4527_);
v___y_4568_ = v_us_4566_;
goto v___jp_4567_;
}
v___jp_4567_:
{
lean_object* v___x_4569_; 
v___x_4569_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4565_, v___y_4568_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v_fst_4571_; lean_object* v_snd_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
lean_dec_ref_known(v___x_4569_, 1);
v_fst_4571_ = lean_ctor_get(v_a_4570_, 0);
lean_inc(v_fst_4571_);
v_snd_4572_ = lean_ctor_get(v_a_4570_, 1);
lean_inc(v_snd_4572_);
lean_dec(v_a_4570_);
v___x_4573_ = lean_unsigned_to_nat(0u);
v___x_4574_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_snd_4572_, v_fst_4571_, v___x_4573_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
return v___x_4574_;
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
v_a_4575_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4569_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4569_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v_fn_4587_ = lean_ctor_get(v_x_4528_, 0);
lean_inc_ref(v_fn_4587_);
lean_dec_ref_known(v_x_4528_, 2);
v___x_4588_ = lean_unsigned_to_nat(1u);
v___x_4589_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_00_u03c3_4527_, v_fn_4587_, v___x_4588_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
return v___x_4589_;
}
case 6:
{
uint8_t v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
lean_dec_ref_known(v_x_4528_, 3);
lean_dec_ref(v_00_u03c3_4527_);
v___x_4590_ = 0;
v___x_4591_ = lean_box(v___x_4590_);
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
return v___x_4592_;
}
case 7:
{
lean_object* v_body_4593_; 
v_body_4593_ = lean_ctor_get(v_x_4528_, 2);
lean_inc_ref(v_body_4593_);
lean_dec_ref_known(v_x_4528_, 3);
v_x_4528_ = v_body_4593_;
goto _start;
}
case 8:
{
lean_object* v_body_4595_; 
v_body_4595_ = lean_ctor_get(v_x_4528_, 3);
lean_inc_ref(v_body_4595_);
lean_dec_ref_known(v_x_4528_, 4);
v_x_4528_ = v_body_4595_;
goto _start;
}
case 9:
{
uint8_t v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
lean_dec_ref_known(v_x_4528_, 1);
lean_dec_ref(v_00_u03c3_4527_);
v___x_4597_ = 0;
v___x_4598_ = lean_box(v___x_4597_);
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
return v___x_4599_;
}
case 10:
{
lean_object* v_expr_4600_; 
v_expr_4600_ = lean_ctor_get(v_x_4528_, 1);
lean_inc_ref(v_expr_4600_);
lean_dec_ref_known(v_x_4528_, 2);
v_x_4528_ = v_expr_4600_;
goto _start;
}
default: 
{
uint8_t v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
lean_dec_ref(v_x_4528_);
lean_dec_ref(v_00_u03c3_4527_);
v___x_4602_ = 2;
v___x_4603_ = lean_box(v___x_4602_);
v___x_4604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4603_);
return v___x_4604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore___boxed(lean_object* v_00_u03c3_4605_, lean_object* v_x_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4605_, v_x_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_e_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4620_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v___x_4619_, v_e_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_e_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l_Lean_Meta_isPropQuick(v_e_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v___x_4634_; 
lean_inc_ref(v_e_4628_);
v___x_4634_ = l_Lean_Meta_isPropQuick(v_e_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4691_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4637_ = v___x_4634_;
v_isShared_4638_ = v_isSharedCheck_4691_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4634_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4691_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
uint8_t v___x_4639_; 
v___x_4639_ = lean_unbox(v_a_4635_);
lean_dec(v_a_4635_);
switch(v___x_4639_)
{
case 0:
{
uint8_t v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
lean_dec_ref(v_e_4628_);
v___x_4640_ = 0;
v___x_4641_ = lean_box(v___x_4640_);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 0, v___x_4641_);
v___x_4643_ = v___x_4637_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4641_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
case 1:
{
uint8_t v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
lean_dec_ref(v_e_4628_);
v___x_4645_ = 1;
v___x_4646_ = lean_box(v___x_4645_);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 0, v___x_4646_);
v___x_4648_ = v___x_4637_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4646_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
default: 
{
lean_object* v___x_4650_; 
lean_del_object(v___x_4637_);
lean_inc(v_a_4632_);
lean_inc_ref(v_a_4631_);
lean_inc(v_a_4630_);
lean_inc_ref(v_a_4629_);
v___x_4650_ = lean_infer_type(v_e_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v___x_4652_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4650_, 1);
v___x_4652_ = l_Lean_Meta_whnfD(v_a_4651_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4674_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4655_ = v___x_4652_;
v_isShared_4656_ = v_isSharedCheck_4674_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4652_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4674_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
if (lean_obj_tag(v_a_4653_) == 3)
{
lean_object* v_u_4657_; lean_object* v___x_4658_; lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4668_; 
lean_del_object(v___x_4655_);
v_u_4657_ = lean_ctor_get(v_a_4653_, 0);
lean_inc(v_u_4657_);
lean_dec_ref_known(v_a_4653_, 1);
v___x_4658_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4657_, v_a_4630_);
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4668_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4668_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
uint8_t v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4666_; 
v___x_4663_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4659_);
lean_dec(v_a_4659_);
v___x_4664_ = lean_box(v___x_4663_);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4664_);
v___x_4666_ = v___x_4661_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4664_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
else
{
uint8_t v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4672_; 
lean_dec(v_a_4653_);
v___x_4669_ = 0;
v___x_4670_ = lean_box(v___x_4669_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v___x_4670_);
v___x_4672_ = v___x_4655_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4670_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
v_a_4675_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4652_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4652_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4675_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
v_a_4683_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4650_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4650_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
lean_dec_ref(v_e_4628_);
v_a_4692_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4634_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_dec(v___x_4634_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_Lean_Meta_isProp(v_e_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4707_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = lean_obj_tag_nat(v_x_4707_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4709_);
lean_dec(v_x_4709_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4711_, lean_object* v_k_4712_){
_start:
{
if (lean_obj_tag(v_t_4711_) == 3)
{
lean_object* v_idx_4713_; lean_object* v_numArgs_4714_; lean_object* v___x_4715_; 
v_idx_4713_ = lean_ctor_get(v_t_4711_, 0);
lean_inc(v_idx_4713_);
v_numArgs_4714_ = lean_ctor_get(v_t_4711_, 1);
lean_inc(v_numArgs_4714_);
lean_dec_ref_known(v_t_4711_, 2);
v___x_4715_ = lean_apply_2(v_k_4712_, v_idx_4713_, v_numArgs_4714_);
return v___x_4715_;
}
else
{
lean_dec(v_t_4711_);
return v_k_4712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4716_, lean_object* v_ctorIdx_4717_, lean_object* v_t_4718_, lean_object* v_h_4719_, lean_object* v_k_4720_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4718_, v_k_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4722_, lean_object* v_ctorIdx_4723_, lean_object* v_t_4724_, lean_object* v_h_4725_, lean_object* v_k_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4722_, v_ctorIdx_4723_, v_t_4724_, v_h_4725_, v_k_4726_);
lean_dec(v_ctorIdx_4723_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4728_, lean_object* v_false_4729_){
_start:
{
lean_object* v___x_4730_; 
v___x_4730_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4728_, v_false_4729_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4731_, lean_object* v_t_4732_, lean_object* v_h_4733_, lean_object* v_false_4734_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4732_, v_false_4734_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4736_, lean_object* v_true_4737_){
_start:
{
lean_object* v___x_4738_; 
v___x_4738_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4736_, v_true_4737_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4739_, lean_object* v_t_4740_, lean_object* v_h_4741_, lean_object* v_true_4742_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4740_, v_true_4742_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4744_, lean_object* v_undef_4745_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4744_, v_undef_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4747_, lean_object* v_t_4748_, lean_object* v_h_4749_, lean_object* v_undef_4750_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4748_, v_undef_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4752_, lean_object* v_bvar_4753_){
_start:
{
lean_object* v___x_4754_; 
v___x_4754_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4752_, v_bvar_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4755_, lean_object* v_t_4756_, lean_object* v_h_4757_, lean_object* v_bvar_4758_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4756_, v_bvar_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4760_){
_start:
{
switch(v_x_4760_)
{
case 0:
{
lean_object* v___x_4761_; 
v___x_4761_ = lean_box(0);
return v___x_4761_;
}
case 1:
{
lean_object* v___x_4762_; 
v___x_4762_ = lean_box(1);
return v___x_4762_;
}
default: 
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_box(2);
return v___x_4763_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4764_){
_start:
{
uint8_t v_x_25__boxed_4765_; lean_object* v_res_4766_; 
v_x_25__boxed_4765_ = lean_unbox(v_x_4764_);
v_res_4766_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4765_);
return v_res_4766_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4767_){
_start:
{
switch(lean_obj_tag(v_x_4767_))
{
case 0:
{
uint8_t v___x_4768_; 
v___x_4768_ = 0;
return v___x_4768_;
}
case 1:
{
uint8_t v___x_4769_; 
v___x_4769_ = 1;
return v___x_4769_;
}
default: 
{
uint8_t v___x_4770_; 
v___x_4770_ = 2;
return v___x_4770_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4771_){
_start:
{
uint8_t v_res_4772_; lean_object* v_r_4773_; 
v_res_4772_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4771_);
lean_dec(v_x_4771_);
v_r_4773_ = lean_box(v_res_4772_);
return v_r_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_00_u03c3_4775_, lean_object* v_e_4776_, lean_object* v_numArgs_4777_){
_start:
{
lean_object* v___y_4779_; 
switch(lean_obj_tag(v_e_4776_))
{
case 3:
{
lean_object* v_u_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
v_u_4785_ = lean_ctor_get(v_e_4776_, 0);
lean_inc(v_u_4785_);
lean_dec_ref_known(v_e_4776_, 1);
v___x_4786_ = lean_unsigned_to_nat(0u);
v___x_4787_ = lean_nat_dec_eq(v_numArgs_4777_, v___x_4786_);
lean_dec(v_numArgs_4777_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; 
lean_dec(v_u_4785_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4788_ = lean_box(2);
return v___x_4788_;
}
else
{
lean_object* v_paramNames_4789_; lean_object* v_lvls_4790_; uint8_t v___x_4791_; 
v_paramNames_4789_ = lean_ctor_get(v_00_u03c3_4775_, 0);
lean_inc(v_paramNames_4789_);
v_lvls_4790_ = lean_ctor_get(v_00_u03c3_4775_, 1);
lean_inc(v_lvls_4790_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4791_ = l_List_isEmpty___redArg(v_paramNames_4789_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; 
v___x_4792_ = l_Lean_Level_instantiateParams(v_u_4785_, v_paramNames_4789_, v_lvls_4790_);
v___y_4779_ = v___x_4792_;
goto v___jp_4778_;
}
else
{
lean_dec(v_lvls_4790_);
lean_dec(v_paramNames_4789_);
v___y_4779_ = v_u_4785_;
goto v___jp_4778_;
}
}
}
case 7:
{
lean_object* v_body_4793_; lean_object* v_zero_4794_; uint8_t v_isZero_4795_; 
v_body_4793_ = lean_ctor_get(v_e_4776_, 2);
lean_inc_ref(v_body_4793_);
lean_dec_ref_known(v_e_4776_, 3);
v_zero_4794_ = lean_unsigned_to_nat(0u);
v_isZero_4795_ = lean_nat_dec_eq(v_numArgs_4777_, v_zero_4794_);
if (v_isZero_4795_ == 0)
{
lean_object* v_one_4796_; lean_object* v_n_4797_; 
v_one_4796_ = lean_unsigned_to_nat(1u);
v_n_4797_ = lean_nat_sub(v_numArgs_4777_, v_one_4796_);
lean_dec(v_numArgs_4777_);
v_e_4776_ = v_body_4793_;
v_numArgs_4777_ = v_n_4797_;
goto _start;
}
else
{
lean_object* v___x_4799_; 
lean_dec_ref(v_body_4793_);
lean_dec(v_numArgs_4777_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4799_ = lean_box(2);
return v___x_4799_;
}
}
case 10:
{
lean_object* v_expr_4800_; 
v_expr_4800_ = lean_ctor_get(v_e_4776_, 1);
lean_inc_ref(v_expr_4800_);
lean_dec_ref_known(v_e_4776_, 2);
v_e_4776_ = v_expr_4800_;
goto _start;
}
case 5:
{
lean_object* v_fn_4802_; 
v_fn_4802_ = lean_ctor_get(v_e_4776_, 0);
if (lean_obj_tag(v_fn_4802_) == 4)
{
lean_object* v_declName_4803_; 
v_declName_4803_ = lean_ctor_get(v_fn_4802_, 0);
lean_inc(v_declName_4803_);
if (lean_obj_tag(v_declName_4803_) == 1)
{
lean_object* v_pre_4804_; 
v_pre_4804_ = lean_ctor_get(v_declName_4803_, 0);
if (lean_obj_tag(v_pre_4804_) == 0)
{
lean_object* v_arg_4805_; lean_object* v_str_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v_arg_4805_ = lean_ctor_get(v_e_4776_, 1);
lean_inc_ref(v_arg_4805_);
lean_dec_ref_known(v_e_4776_, 2);
v_str_4806_ = lean_ctor_get(v_declName_4803_, 1);
lean_inc_ref(v_str_4806_);
lean_dec_ref_known(v_declName_4803_, 2);
v___x_4807_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4808_ = lean_string_dec_eq(v_str_4806_, v___x_4807_);
lean_dec_ref(v_str_4806_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4809_; 
lean_dec_ref(v_arg_4805_);
lean_dec(v_numArgs_4777_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4809_ = lean_box(2);
return v___x_4809_;
}
else
{
v_e_4776_ = v_arg_4805_;
goto _start;
}
}
else
{
lean_object* v___x_4811_; 
lean_dec_ref_known(v_declName_4803_, 2);
lean_dec_ref_known(v_e_4776_, 2);
lean_dec(v_numArgs_4777_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4811_ = lean_box(2);
return v___x_4811_;
}
}
else
{
lean_object* v___x_4812_; 
lean_dec(v_declName_4803_);
lean_dec_ref_known(v_e_4776_, 2);
lean_dec(v_numArgs_4777_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4812_ = lean_box(2);
return v___x_4812_;
}
}
else
{
lean_object* v___x_4813_; 
lean_dec_ref_known(v_e_4776_, 2);
lean_dec(v_numArgs_4777_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4813_ = lean_box(2);
return v___x_4813_;
}
}
default: 
{
lean_object* v___x_4814_; 
lean_dec(v_numArgs_4777_);
lean_dec_ref(v_e_4776_);
lean_dec_ref(v_00_u03c3_4775_);
v___x_4814_ = lean_box(2);
return v___x_4814_;
}
}
v___jp_4778_:
{
uint8_t v___x_4780_; 
v___x_4780_ = l_Lean_Level_isNeverZero(v___y_4779_);
if (v___x_4780_ == 0)
{
uint8_t v___x_4781_; 
v___x_4781_ = l_Lean_Level_isZero(v___y_4779_);
lean_dec(v___y_4779_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; 
v___x_4782_ = lean_box(2);
return v___x_4782_;
}
else
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_box(1);
return v___x_4783_;
}
}
else
{
lean_object* v___x_4784_; 
lean_dec(v___y_4779_);
v___x_4784_ = lean_box(0);
return v___x_4784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_00_u03c3_4815_, lean_object* v_r_4816_, lean_object* v_binderType_4817_){
_start:
{
if (lean_obj_tag(v_r_4816_) == 3)
{
lean_object* v_idx_4818_; lean_object* v_numArgs_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4831_; 
v_idx_4818_ = lean_ctor_get(v_r_4816_, 0);
v_numArgs_4819_ = lean_ctor_get(v_r_4816_, 1);
v_isSharedCheck_4831_ = !lean_is_exclusive(v_r_4816_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4821_ = v_r_4816_;
v_isShared_4822_ = v_isSharedCheck_4831_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_numArgs_4819_);
lean_inc(v_idx_4818_);
lean_dec(v_r_4816_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4831_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v_zero_4823_; uint8_t v_isZero_4824_; 
v_zero_4823_ = lean_unsigned_to_nat(0u);
v_isZero_4824_ = lean_nat_dec_eq(v_idx_4818_, v_zero_4823_);
if (v_isZero_4824_ == 1)
{
lean_object* v___x_4825_; 
lean_del_object(v___x_4821_);
lean_dec(v_idx_4818_);
v___x_4825_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_00_u03c3_4815_, v_binderType_4817_, v_numArgs_4819_);
return v___x_4825_;
}
else
{
lean_object* v_one_4826_; lean_object* v_n_4827_; lean_object* v___x_4829_; 
lean_dec_ref(v_binderType_4817_);
lean_dec_ref(v_00_u03c3_4815_);
v_one_4826_ = lean_unsigned_to_nat(1u);
v_n_4827_ = lean_nat_sub(v_idx_4818_, v_one_4826_);
lean_dec(v_idx_4818_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v_n_4827_);
v___x_4829_ = v___x_4821_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_n_4827_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_numArgs_4819_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_4817_);
lean_dec_ref(v_00_u03c3_4815_);
return v_r_4816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_00_u03c3_4832_, lean_object* v_x_4833_, lean_object* v_x_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_type_4841_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; 
switch(lean_obj_tag(v_x_4833_))
{
case 7:
{
lean_object* v_binderType_4873_; lean_object* v_body_4874_; lean_object* v_zero_4875_; uint8_t v_isZero_4876_; 
v_binderType_4873_ = lean_ctor_get(v_x_4833_, 1);
v_body_4874_ = lean_ctor_get(v_x_4833_, 2);
v_zero_4875_ = lean_unsigned_to_nat(0u);
v_isZero_4876_ = lean_nat_dec_eq(v_x_4834_, v_zero_4875_);
if (v_isZero_4876_ == 1)
{
v_type_4841_ = v_x_4833_;
v___y_4842_ = v_a_4835_;
v___y_4843_ = v_a_4836_;
v___y_4844_ = v_a_4837_;
v___y_4845_ = v_a_4838_;
goto v___jp_4840_;
}
else
{
lean_object* v_one_4877_; lean_object* v_n_4878_; lean_object* v___x_4879_; 
lean_inc_ref(v_body_4874_);
lean_inc_ref(v_binderType_4873_);
lean_dec_ref_known(v_x_4833_, 3);
v_one_4877_ = lean_unsigned_to_nat(1u);
v_n_4878_ = lean_nat_sub(v_x_4834_, v_one_4877_);
lean_inc_ref(v_00_u03c3_4832_);
v___x_4879_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4832_, v_body_4874_, v_n_4878_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
lean_dec(v_n_4878_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4888_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4888_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4888_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4884_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4832_, v_a_4880_, v_binderType_4873_);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4884_);
v___x_4886_ = v___x_4882_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
else
{
lean_dec_ref(v_binderType_4873_);
lean_dec_ref(v_00_u03c3_4832_);
return v___x_4879_;
}
}
}
case 8:
{
lean_object* v_type_4889_; lean_object* v_body_4890_; lean_object* v___x_4891_; 
v_type_4889_ = lean_ctor_get(v_x_4833_, 1);
lean_inc_ref(v_type_4889_);
v_body_4890_ = lean_ctor_get(v_x_4833_, 3);
lean_inc_ref(v_body_4890_);
lean_dec_ref_known(v_x_4833_, 4);
lean_inc_ref(v_00_u03c3_4832_);
v___x_4891_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4832_, v_body_4890_, v_x_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4900_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4894_ = v___x_4891_;
v_isShared_4895_ = v_isSharedCheck_4900_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4900_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4896_; lean_object* v___x_4898_; 
v___x_4896_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_00_u03c3_4832_, v_a_4892_, v_type_4889_);
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4896_);
v___x_4898_ = v___x_4894_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4896_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
else
{
lean_dec_ref(v_type_4889_);
lean_dec_ref(v_00_u03c3_4832_);
return v___x_4891_;
}
}
case 10:
{
lean_object* v_expr_4901_; 
v_expr_4901_ = lean_ctor_get(v_x_4833_, 1);
lean_inc_ref(v_expr_4901_);
lean_dec_ref_known(v_x_4833_, 2);
v_x_4833_ = v_expr_4901_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4903_; lean_object* v___x_4904_; uint8_t v___x_4905_; 
lean_dec_ref(v_00_u03c3_4832_);
v_deBruijnIndex_4903_ = lean_ctor_get(v_x_4833_, 0);
lean_inc(v_deBruijnIndex_4903_);
lean_dec_ref_known(v_x_4833_, 1);
v___x_4904_ = lean_unsigned_to_nat(0u);
v___x_4905_ = lean_nat_dec_eq(v_x_4834_, v___x_4904_);
if (v___x_4905_ == 0)
{
lean_dec(v_deBruijnIndex_4903_);
goto v___jp_4870_;
}
else
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
v___x_4906_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4906_, 0, v_deBruijnIndex_4903_);
lean_ctor_set(v___x_4906_, 1, v___x_4904_);
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
return v___x_4907_;
}
}
default: 
{
lean_object* v___x_4908_; uint8_t v___x_4909_; 
v___x_4908_ = lean_unsigned_to_nat(0u);
v___x_4909_ = lean_nat_dec_eq(v_x_4834_, v___x_4908_);
if (v___x_4909_ == 0)
{
lean_dec_ref(v_x_4833_);
lean_dec_ref(v_00_u03c3_4832_);
goto v___jp_4870_;
}
else
{
v_type_4841_ = v_x_4833_;
v___y_4842_ = v_a_4835_;
v___y_4843_ = v_a_4836_;
v___y_4844_ = v_a_4837_;
v___y_4845_ = v_a_4838_;
goto v___jp_4840_;
}
}
}
v___jp_4840_:
{
lean_object* v___x_4846_; 
v___x_4846_ = l_Lean_Expr_getAppFn(v_type_4841_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_deBruijnIndex_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
lean_dec_ref(v_00_u03c3_4832_);
v_deBruijnIndex_4847_ = lean_ctor_get(v___x_4846_, 0);
lean_inc(v_deBruijnIndex_4847_);
lean_dec_ref_known(v___x_4846_, 1);
v___x_4848_ = l_Lean_Expr_getAppNumArgs(v_type_4841_);
lean_dec_ref(v_type_4841_);
v___x_4849_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4849_, 0, v_deBruijnIndex_4847_);
lean_ctor_set(v___x_4849_, 1, v___x_4848_);
v___x_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4849_);
return v___x_4850_;
}
else
{
lean_object* v___x_4851_; 
lean_dec_ref(v___x_4846_);
v___x_4851_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickCore(v_00_u03c3_4832_, v_type_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4861_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4861_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4861_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4859_; 
v___x_4856_ = lean_unbox(v_a_4852_);
lean_dec(v_a_4852_);
v___x_4857_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4856_);
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
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
v_a_4862_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4851_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4851_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
}
v___jp_4870_:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = lean_box(2);
v___x_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
return v___x_4872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_00_u03c3_4910_, lean_object* v_x_4911_, lean_object* v_x_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4910_, v_x_4911_, v_x_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
lean_dec(v_a_4916_);
lean_dec_ref(v_a_4915_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_x_4912_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_00_u03c3_4919_, lean_object* v_e_4920_, lean_object* v_n_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_00_u03c3_4919_, v_e_4920_, v_n_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4937_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4937_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4937_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
uint8_t v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v___x_4932_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4928_);
lean_dec(v_a_4928_);
v___x_4933_ = lean_box(v___x_4932_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v___x_4933_);
v___x_4935_ = v___x_4930_;
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
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
v_a_4938_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4927_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4927_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_00_u03c3_4946_, lean_object* v_e_4947_, lean_object* v_n_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_00_u03c3_4946_, v_e_4947_, v_n_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_n_4948_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
switch(lean_obj_tag(v_x_4955_))
{
case 1:
{
lean_object* v_fvarId_4961_; lean_object* v___x_4962_; 
v_fvarId_4961_ = lean_ctor_get(v_x_4955_, 0);
lean_inc(v_fvarId_4961_);
lean_dec_ref_known(v_x_4955_, 1);
v___x_4962_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4961_, v_a_4956_, v_a_4958_, v_a_4959_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_a_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4964_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4965_ = lean_unsigned_to_nat(0u);
v___x_4966_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4964_, v_a_4963_, v___x_4965_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
return v___x_4966_;
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
v_a_4967_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4962_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4962_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4975_; lean_object* v___x_4976_; 
v_mvarId_4975_ = lean_ctor_get(v_x_4955_, 0);
lean_inc(v_mvarId_4975_);
lean_dec_ref_known(v_x_4955_, 1);
v___x_4976_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4975_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4976_, 1);
v___x_4978_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_4979_ = lean_unsigned_to_nat(0u);
v___x_4980_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_4978_, v_a_4977_, v___x_4979_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
return v___x_4980_;
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
v_a_4981_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4976_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4976_);
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
case 3:
{
uint8_t v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
lean_dec_ref_known(v_x_4955_, 1);
v___x_4989_ = 0;
v___x_4990_ = lean_box(v___x_4989_);
v___x_4991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4990_);
return v___x_4991_;
}
case 4:
{
lean_object* v_declName_4992_; lean_object* v_us_4993_; lean_object* v___x_4994_; 
v_declName_4992_ = lean_ctor_get(v_x_4955_, 0);
lean_inc(v_declName_4992_);
v_us_4993_ = lean_ctor_get(v_x_4955_, 1);
lean_inc(v_us_4993_);
lean_dec_ref_known(v_x_4955_, 2);
v___x_4994_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_4992_, v_us_4993_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; lean_object* v_fst_4996_; lean_object* v_snd_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
lean_dec_ref_known(v___x_4994_, 1);
v_fst_4996_ = lean_ctor_get(v_a_4995_, 0);
lean_inc(v_fst_4996_);
v_snd_4997_ = lean_ctor_get(v_a_4995_, 1);
lean_inc(v_snd_4997_);
lean_dec(v_a_4995_);
v___x_4998_ = lean_unsigned_to_nat(0u);
v___x_4999_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_4997_, v_fst_4996_, v___x_4998_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
return v___x_4999_;
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
v_a_5000_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4994_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4994_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
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
case 5:
{
lean_object* v_fn_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v_fn_5008_ = lean_ctor_get(v_x_4955_, 0);
lean_inc_ref(v_fn_5008_);
lean_dec_ref_known(v_x_4955_, 2);
v___x_5009_ = lean_unsigned_to_nat(1u);
v___x_5010_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_5008_, v___x_5009_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
return v___x_5010_;
}
case 6:
{
lean_object* v_body_5011_; 
v_body_5011_ = lean_ctor_get(v_x_4955_, 2);
lean_inc_ref(v_body_5011_);
lean_dec_ref_known(v_x_4955_, 3);
v_x_4955_ = v_body_5011_;
goto _start;
}
case 7:
{
uint8_t v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
lean_dec_ref_known(v_x_4955_, 3);
v___x_5013_ = 0;
v___x_5014_ = lean_box(v___x_5013_);
v___x_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5014_);
return v___x_5015_;
}
case 8:
{
lean_object* v_body_5016_; 
v_body_5016_ = lean_ctor_get(v_x_4955_, 3);
lean_inc_ref(v_body_5016_);
lean_dec_ref_known(v_x_4955_, 4);
v_x_4955_ = v_body_5016_;
goto _start;
}
case 9:
{
uint8_t v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
lean_dec_ref_known(v_x_4955_, 1);
v___x_5018_ = 0;
v___x_5019_ = lean_box(v___x_5018_);
v___x_5020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
return v___x_5020_;
}
case 10:
{
lean_object* v_expr_5021_; 
v_expr_5021_ = lean_ctor_get(v_x_4955_, 1);
lean_inc_ref(v_expr_5021_);
lean_dec_ref_known(v_x_4955_, 2);
v_x_4955_ = v_expr_5021_;
goto _start;
}
default: 
{
uint8_t v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
lean_dec_ref(v_x_4955_);
v___x_5023_ = 2;
v___x_5024_ = lean_box(v___x_5023_);
v___x_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5024_);
return v___x_5025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_5026_, lean_object* v_x_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_){
_start:
{
switch(lean_obj_tag(v_x_5026_))
{
case 4:
{
lean_object* v_declName_5033_; lean_object* v_us_5034_; lean_object* v___x_5035_; 
v_declName_5033_ = lean_ctor_get(v_x_5026_, 0);
lean_inc(v_declName_5033_);
v_us_5034_ = lean_ctor_get(v_x_5026_, 1);
lean_inc(v_us_5034_);
lean_dec_ref_known(v_x_5026_, 2);
v___x_5035_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5033_, v_us_5034_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v_fst_5037_; lean_object* v_snd_5038_; lean_object* v___x_5039_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5035_, 1);
v_fst_5037_ = lean_ctor_get(v_a_5036_, 0);
lean_inc(v_fst_5037_);
v_snd_5038_ = lean_ctor_get(v_a_5036_, 1);
lean_inc(v_snd_5038_);
lean_dec(v_a_5036_);
v___x_5039_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_snd_5038_, v_fst_5037_, v_x_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
lean_dec(v_x_5027_);
return v___x_5039_;
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_dec(v_x_5027_);
v_a_5040_ = lean_ctor_get(v___x_5035_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_5035_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5035_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_5048_; lean_object* v___x_5049_; 
v_fvarId_5048_ = lean_ctor_get(v_x_5026_, 0);
lean_inc(v_fvarId_5048_);
lean_dec_ref_known(v_x_5026_, 1);
v___x_5049_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5048_, v_a_5028_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___x_5049_, 1);
v___x_5051_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5052_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5051_, v_a_5050_, v_x_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
lean_dec(v_x_5027_);
return v___x_5052_;
}
else
{
lean_object* v_a_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5060_; 
lean_dec(v_x_5027_);
v_a_5053_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5055_ = v___x_5049_;
v_isShared_5056_ = v_isSharedCheck_5060_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_a_5053_);
lean_dec(v___x_5049_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5060_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5058_; 
if (v_isShared_5056_ == 0)
{
v___x_5058_ = v___x_5055_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5053_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
return v___x_5058_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5061_; lean_object* v___x_5062_; 
v_mvarId_5061_ = lean_ctor_get(v_x_5026_, 0);
lean_inc(v_mvarId_5061_);
lean_dec_ref_known(v_x_5026_, 1);
v___x_5062_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5061_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5062_, 1);
v___x_5064_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___closed__0));
v___x_5065_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v___x_5064_, v_a_5063_, v_x_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
lean_dec(v_x_5027_);
return v___x_5065_;
}
else
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5073_; 
lean_dec(v_x_5027_);
v_a_5066_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5068_ = v___x_5062_;
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v___x_5062_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5071_; 
if (v_isShared_5069_ == 0)
{
v___x_5071_ = v___x_5068_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5066_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
case 5:
{
lean_object* v_fn_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v_fn_5074_ = lean_ctor_get(v_x_5026_, 0);
lean_inc_ref(v_fn_5074_);
lean_dec_ref_known(v_x_5026_, 2);
v___x_5075_ = lean_unsigned_to_nat(1u);
v___x_5076_ = lean_nat_add(v_x_5027_, v___x_5075_);
lean_dec(v_x_5027_);
v_x_5026_ = v_fn_5074_;
v_x_5027_ = v___x_5076_;
goto _start;
}
case 10:
{
lean_object* v_expr_5078_; 
v_expr_5078_ = lean_ctor_get(v_x_5026_, 1);
lean_inc_ref(v_expr_5078_);
lean_dec_ref_known(v_x_5026_, 2);
v_x_5026_ = v_expr_5078_;
goto _start;
}
case 8:
{
lean_object* v_body_5080_; 
v_body_5080_ = lean_ctor_get(v_x_5026_, 3);
lean_inc_ref(v_body_5080_);
lean_dec_ref_known(v_x_5026_, 4);
v_x_5026_ = v_body_5080_;
goto _start;
}
case 6:
{
lean_object* v_body_5082_; lean_object* v_zero_5083_; uint8_t v_isZero_5084_; 
v_body_5082_ = lean_ctor_get(v_x_5026_, 2);
lean_inc_ref(v_body_5082_);
lean_dec_ref_known(v_x_5026_, 3);
v_zero_5083_ = lean_unsigned_to_nat(0u);
v_isZero_5084_ = lean_nat_dec_eq(v_x_5027_, v_zero_5083_);
if (v_isZero_5084_ == 1)
{
lean_object* v___x_5085_; 
lean_dec(v_x_5027_);
v___x_5085_ = l_Lean_Meta_isProofQuick(v_body_5082_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
return v___x_5085_;
}
else
{
lean_object* v_one_5086_; lean_object* v_n_5087_; 
v_one_5086_ = lean_unsigned_to_nat(1u);
v_n_5087_ = lean_nat_sub(v_x_5027_, v_one_5086_);
lean_dec(v_x_5027_);
v_x_5026_ = v_body_5082_;
v_x_5027_ = v_n_5087_;
goto _start;
}
}
default: 
{
uint8_t v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
lean_dec(v_x_5027_);
lean_dec_ref(v_x_5026_);
v___x_5089_ = 2;
v___x_5090_ = lean_box(v___x_5089_);
v___x_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5090_);
return v___x_5091_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_5092_, lean_object* v_x_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_5092_, v_x_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Lean_Meta_isProofQuick(v_x_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
lean_dec(v_a_5104_);
lean_dec_ref(v_a_5103_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v___x_5113_; 
lean_inc_ref(v_e_5107_);
v___x_5113_ = l_Lean_Meta_isProofQuick(v_e_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5140_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5140_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5140_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
uint8_t v___x_5118_; 
v___x_5118_ = lean_unbox(v_a_5114_);
lean_dec(v_a_5114_);
switch(v___x_5118_)
{
case 0:
{
uint8_t v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5122_; 
lean_dec_ref(v_e_5107_);
v___x_5119_ = 0;
v___x_5120_ = lean_box(v___x_5119_);
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 0, v___x_5120_);
v___x_5122_ = v___x_5116_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5120_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
case 1:
{
uint8_t v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5127_; 
lean_dec_ref(v_e_5107_);
v___x_5124_ = 1;
v___x_5125_ = lean_box(v___x_5124_);
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 0, v___x_5125_);
v___x_5127_ = v___x_5116_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5125_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
default: 
{
lean_object* v___x_5129_; 
lean_del_object(v___x_5116_);
lean_inc(v_a_5111_);
lean_inc_ref(v_a_5110_);
lean_inc(v_a_5109_);
lean_inc_ref(v_a_5108_);
v___x_5129_ = lean_infer_type(v_e_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5131_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v___x_5131_ = l_Lean_Meta_isProp(v_a_5130_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
return v___x_5131_;
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
v_a_5132_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5129_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5129_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5148_; 
lean_dec_ref(v_e_5107_);
v_a_5141_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5143_ = v___x_5113_;
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5113_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5146_; 
if (v_isShared_5144_ == 0)
{
v___x_5146_ = v___x_5143_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5141_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_Lean_Meta_isProof(v_e_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_);
lean_dec(v_a_5153_);
lean_dec_ref(v_a_5152_);
lean_dec(v_a_5151_);
lean_dec_ref(v_a_5150_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_5156_, lean_object* v_x_5157_){
_start:
{
switch(lean_obj_tag(v_x_5156_))
{
case 3:
{
lean_object* v___x_5163_; uint8_t v___x_5164_; 
v___x_5163_ = lean_unsigned_to_nat(0u);
v___x_5164_ = lean_nat_dec_eq(v_x_5157_, v___x_5163_);
lean_dec(v_x_5157_);
if (v___x_5164_ == 0)
{
goto v___jp_5159_;
}
else
{
uint8_t v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
v___x_5165_ = 1;
v___x_5166_ = lean_box(v___x_5165_);
v___x_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5166_);
return v___x_5167_;
}
}
case 7:
{
lean_object* v_body_5168_; lean_object* v_zero_5169_; uint8_t v_isZero_5170_; 
v_body_5168_ = lean_ctor_get(v_x_5156_, 2);
v_zero_5169_ = lean_unsigned_to_nat(0u);
v_isZero_5170_ = lean_nat_dec_eq(v_x_5157_, v_zero_5169_);
if (v_isZero_5170_ == 1)
{
uint8_t v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
lean_dec(v_x_5157_);
v___x_5171_ = 0;
v___x_5172_ = lean_box(v___x_5171_);
v___x_5173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5173_, 0, v___x_5172_);
return v___x_5173_;
}
else
{
lean_object* v_one_5174_; lean_object* v_n_5175_; 
v_one_5174_ = lean_unsigned_to_nat(1u);
v_n_5175_ = lean_nat_sub(v_x_5157_, v_one_5174_);
lean_dec(v_x_5157_);
v_x_5156_ = v_body_5168_;
v_x_5157_ = v_n_5175_;
goto _start;
}
}
case 8:
{
lean_object* v_body_5177_; 
v_body_5177_ = lean_ctor_get(v_x_5156_, 3);
v_x_5156_ = v_body_5177_;
goto _start;
}
case 10:
{
lean_object* v_expr_5179_; 
v_expr_5179_ = lean_ctor_get(v_x_5156_, 1);
v_x_5156_ = v_expr_5179_;
goto _start;
}
default: 
{
lean_dec(v_x_5157_);
goto v___jp_5159_;
}
}
v___jp_5159_:
{
uint8_t v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5160_ = 2;
v___x_5161_ = lean_box(v___x_5160_);
v___x_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5161_);
return v___x_5162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_5181_, lean_object* v_x_5182_, lean_object* v_a_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5181_, v_x_5182_);
lean_dec_ref(v_x_5181_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_5185_, lean_object* v_x_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v___x_5192_; 
v___x_5192_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_5185_, v_x_5186_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_5193_, lean_object* v_x_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_5193_, v_x_5194_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_);
lean_dec(v_a_5198_);
lean_dec_ref(v_a_5197_);
lean_dec(v_a_5196_);
lean_dec_ref(v_a_5195_);
lean_dec_ref(v_x_5193_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_5201_, lean_object* v_x_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_){
_start:
{
switch(lean_obj_tag(v_x_5201_))
{
case 4:
{
lean_object* v_declName_5208_; lean_object* v_us_5209_; lean_object* v___x_5210_; 
v_declName_5208_ = lean_ctor_get(v_x_5201_, 0);
lean_inc(v_declName_5208_);
v_us_5209_ = lean_ctor_get(v_x_5201_, 1);
lean_inc(v_us_5209_);
lean_dec_ref_known(v_x_5201_, 2);
v___x_5210_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5208_, v_us_5209_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_object* v_a_5211_; lean_object* v_fst_5212_; lean_object* v___x_5213_; 
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc(v_a_5211_);
lean_dec_ref_known(v___x_5210_, 1);
v_fst_5212_ = lean_ctor_get(v_a_5211_, 0);
lean_inc(v_fst_5212_);
lean_dec(v_a_5211_);
v___x_5213_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5212_, v_x_5202_);
lean_dec(v_fst_5212_);
return v___x_5213_;
}
else
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
lean_dec(v_x_5202_);
v_a_5214_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v___x_5210_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5210_);
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
case 1:
{
lean_object* v_fvarId_5222_; lean_object* v___x_5223_; 
v_fvarId_5222_ = lean_ctor_get(v_x_5201_, 0);
lean_inc(v_fvarId_5222_);
lean_dec_ref_known(v_x_5201_, 1);
v___x_5223_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5222_, v_a_5203_, v_a_5205_, v_a_5206_);
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_object* v_a_5224_; lean_object* v___x_5225_; 
v_a_5224_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_a_5224_);
lean_dec_ref_known(v___x_5223_, 1);
v___x_5225_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5224_, v_x_5202_);
lean_dec(v_a_5224_);
return v___x_5225_;
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
lean_dec(v_x_5202_);
v_a_5226_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5223_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5223_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_5234_; lean_object* v___x_5235_; 
v_mvarId_5234_ = lean_ctor_get(v_x_5201_, 0);
lean_inc(v_mvarId_5234_);
lean_dec_ref_known(v_x_5201_, 1);
v___x_5235_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5234_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_object* v_a_5236_; lean_object* v___x_5237_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
lean_inc(v_a_5236_);
lean_dec_ref_known(v___x_5235_, 1);
v___x_5237_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5236_, v_x_5202_);
lean_dec(v_a_5236_);
return v___x_5237_;
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
lean_dec(v_x_5202_);
v_a_5238_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5235_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5235_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
case 5:
{
lean_object* v_fn_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
v_fn_5246_ = lean_ctor_get(v_x_5201_, 0);
lean_inc_ref(v_fn_5246_);
lean_dec_ref_known(v_x_5201_, 2);
v___x_5247_ = lean_unsigned_to_nat(1u);
v___x_5248_ = lean_nat_add(v_x_5202_, v___x_5247_);
lean_dec(v_x_5202_);
v_x_5201_ = v_fn_5246_;
v_x_5202_ = v___x_5248_;
goto _start;
}
case 10:
{
lean_object* v_expr_5250_; 
v_expr_5250_ = lean_ctor_get(v_x_5201_, 1);
lean_inc_ref(v_expr_5250_);
lean_dec_ref_known(v_x_5201_, 2);
v_x_5201_ = v_expr_5250_;
goto _start;
}
case 8:
{
lean_object* v_body_5252_; 
v_body_5252_ = lean_ctor_get(v_x_5201_, 3);
lean_inc_ref(v_body_5252_);
lean_dec_ref_known(v_x_5201_, 4);
v_x_5201_ = v_body_5252_;
goto _start;
}
case 6:
{
lean_object* v_body_5254_; lean_object* v_zero_5255_; uint8_t v_isZero_5256_; 
v_body_5254_ = lean_ctor_get(v_x_5201_, 2);
lean_inc_ref(v_body_5254_);
lean_dec_ref_known(v_x_5201_, 3);
v_zero_5255_ = lean_unsigned_to_nat(0u);
v_isZero_5256_ = lean_nat_dec_eq(v_x_5202_, v_zero_5255_);
if (v_isZero_5256_ == 1)
{
uint8_t v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; 
lean_dec_ref(v_body_5254_);
lean_dec(v_x_5202_);
v___x_5257_ = 0;
v___x_5258_ = lean_box(v___x_5257_);
v___x_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5259_, 0, v___x_5258_);
return v___x_5259_;
}
else
{
lean_object* v_one_5260_; lean_object* v_n_5261_; 
v_one_5260_ = lean_unsigned_to_nat(1u);
v_n_5261_ = lean_nat_sub(v_x_5202_, v_one_5260_);
lean_dec(v_x_5202_);
v_x_5201_ = v_body_5254_;
v_x_5202_ = v_n_5261_;
goto _start;
}
}
default: 
{
uint8_t v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
lean_dec(v_x_5202_);
lean_dec_ref(v_x_5201_);
v___x_5263_ = 2;
v___x_5264_ = lean_box(v___x_5263_);
v___x_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5264_);
return v___x_5265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_5266_, lean_object* v_x_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_5266_, v_x_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_){
_start:
{
switch(lean_obj_tag(v_x_5274_))
{
case 1:
{
lean_object* v_fvarId_5280_; lean_object* v___x_5281_; 
v_fvarId_5280_ = lean_ctor_get(v_x_5274_, 0);
lean_inc(v_fvarId_5280_);
lean_dec_ref_known(v_x_5274_, 1);
v___x_5281_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_5280_, v_a_5275_, v_a_5277_, v_a_5278_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_object* v_a_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc(v_a_5282_);
lean_dec_ref_known(v___x_5281_, 1);
v___x_5283_ = lean_unsigned_to_nat(0u);
v___x_5284_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5282_, v___x_5283_);
lean_dec(v_a_5282_);
return v___x_5284_;
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
v_a_5285_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5281_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5281_);
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
case 2:
{
lean_object* v_mvarId_5293_; lean_object* v___x_5294_; 
v_mvarId_5293_ = lean_ctor_get(v_x_5274_, 0);
lean_inc(v_mvarId_5293_);
lean_dec_ref_known(v_x_5274_, 1);
v___x_5294_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_5293_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref_known(v___x_5294_, 1);
v___x_5296_ = lean_unsigned_to_nat(0u);
v___x_5297_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_5295_, v___x_5296_);
lean_dec(v_a_5295_);
return v___x_5297_;
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
v_a_5298_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5294_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5294_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
case 3:
{
uint8_t v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
lean_dec_ref_known(v_x_5274_, 1);
v___x_5306_ = 1;
v___x_5307_ = lean_box(v___x_5306_);
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
return v___x_5308_;
}
case 4:
{
lean_object* v_declName_5309_; lean_object* v_us_5310_; lean_object* v___x_5311_; 
v_declName_5309_ = lean_ctor_get(v_x_5274_, 0);
lean_inc(v_declName_5309_);
v_us_5310_ = lean_ctor_get(v_x_5274_, 1);
lean_inc(v_us_5310_);
lean_dec_ref_known(v_x_5274_, 2);
v___x_5311_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstTypeLazy(v_declName_5309_, v_us_5310_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v_fst_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_a_5312_);
lean_dec_ref_known(v___x_5311_, 1);
v_fst_5313_ = lean_ctor_get(v_a_5312_, 0);
lean_inc(v_fst_5313_);
lean_dec(v_a_5312_);
v___x_5314_ = lean_unsigned_to_nat(0u);
v___x_5315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_fst_5313_, v___x_5314_);
lean_dec(v_fst_5313_);
return v___x_5315_;
}
else
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
v_a_5316_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5311_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5311_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
case 5:
{
lean_object* v_fn_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; 
v_fn_5324_ = lean_ctor_get(v_x_5274_, 0);
lean_inc_ref(v_fn_5324_);
lean_dec_ref_known(v_x_5274_, 2);
v___x_5325_ = lean_unsigned_to_nat(1u);
v___x_5326_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_5324_, v___x_5325_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_);
return v___x_5326_;
}
case 6:
{
uint8_t v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; 
lean_dec_ref_known(v_x_5274_, 3);
v___x_5327_ = 0;
v___x_5328_ = lean_box(v___x_5327_);
v___x_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5328_);
return v___x_5329_;
}
case 7:
{
uint8_t v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; 
lean_dec_ref_known(v_x_5274_, 3);
v___x_5330_ = 1;
v___x_5331_ = lean_box(v___x_5330_);
v___x_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5331_);
return v___x_5332_;
}
case 8:
{
lean_object* v_body_5333_; 
v_body_5333_ = lean_ctor_get(v_x_5274_, 3);
lean_inc_ref(v_body_5333_);
lean_dec_ref_known(v_x_5274_, 4);
v_x_5274_ = v_body_5333_;
goto _start;
}
case 9:
{
uint8_t v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; 
lean_dec_ref_known(v_x_5274_, 1);
v___x_5335_ = 0;
v___x_5336_ = lean_box(v___x_5335_);
v___x_5337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
return v___x_5337_;
}
case 10:
{
lean_object* v_expr_5338_; 
v_expr_5338_ = lean_ctor_get(v_x_5274_, 1);
lean_inc_ref(v_expr_5338_);
lean_dec_ref_known(v_x_5274_, 2);
v_x_5274_ = v_expr_5338_;
goto _start;
}
default: 
{
uint8_t v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
lean_dec_ref(v_x_5274_);
v___x_5340_ = 2;
v___x_5341_ = lean_box(v___x_5340_);
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5341_);
return v___x_5342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Lean_Meta_isTypeQuick(v_x_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
lean_dec(v_a_5347_);
lean_dec_ref(v_a_5346_);
lean_dec(v_a_5345_);
lean_dec_ref(v_a_5344_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v___x_5356_; 
lean_inc_ref(v_e_5350_);
v___x_5356_ = l_Lean_Meta_isTypeQuick(v_e_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5406_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5359_ = v___x_5356_;
v_isShared_5360_ = v_isSharedCheck_5406_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5356_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5406_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
uint8_t v___x_5361_; 
v___x_5361_ = lean_unbox(v_a_5357_);
lean_dec(v_a_5357_);
switch(v___x_5361_)
{
case 0:
{
uint8_t v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5365_; 
lean_dec_ref(v_e_5350_);
v___x_5362_ = 0;
v___x_5363_ = lean_box(v___x_5362_);
if (v_isShared_5360_ == 0)
{
lean_ctor_set(v___x_5359_, 0, v___x_5363_);
v___x_5365_ = v___x_5359_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v___x_5363_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
case 1:
{
uint8_t v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5370_; 
lean_dec_ref(v_e_5350_);
v___x_5367_ = 1;
v___x_5368_ = lean_box(v___x_5367_);
if (v_isShared_5360_ == 0)
{
lean_ctor_set(v___x_5359_, 0, v___x_5368_);
v___x_5370_ = v___x_5359_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5368_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
default: 
{
lean_object* v___x_5372_; 
lean_del_object(v___x_5359_);
lean_inc(v_a_5354_);
lean_inc_ref(v_a_5353_);
lean_inc(v_a_5352_);
lean_inc_ref(v_a_5351_);
v___x_5372_ = lean_infer_type(v_e_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v_a_5373_; lean_object* v___x_5374_; 
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v___x_5372_, 1);
v___x_5374_ = l_Lean_Meta_whnfD(v_a_5373_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5389_; 
v_a_5375_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5377_ = v___x_5374_;
v_isShared_5378_ = v_isSharedCheck_5389_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5374_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5389_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
if (lean_obj_tag(v_a_5375_) == 3)
{
uint8_t v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5382_; 
lean_dec_ref_known(v_a_5375_, 1);
v___x_5379_ = 1;
v___x_5380_ = lean_box(v___x_5379_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 0, v___x_5380_);
v___x_5382_ = v___x_5377_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
else
{
uint8_t v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5387_; 
lean_dec(v_a_5375_);
v___x_5384_ = 0;
v___x_5385_ = lean_box(v___x_5384_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 0, v___x_5385_);
v___x_5387_ = v___x_5377_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v___x_5385_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
else
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5397_; 
v_a_5390_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5392_ = v___x_5374_;
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5374_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5395_; 
if (v_isShared_5393_ == 0)
{
v___x_5395_ = v___x_5392_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v_a_5390_);
v___x_5395_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
return v___x_5395_;
}
}
}
}
else
{
lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5405_; 
v_a_5398_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5400_ = v___x_5372_;
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5372_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5403_; 
if (v_isShared_5401_ == 0)
{
v___x_5403_ = v___x_5400_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_a_5398_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5414_; 
lean_dec_ref(v_e_5350_);
v_a_5407_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5409_ = v___x_5356_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5356_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Lean_Meta_isType(v_e_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
lean_dec(v_a_5419_);
lean_dec_ref(v_a_5418_);
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_5422_){
_start:
{
switch(lean_obj_tag(v_x_5422_))
{
case 7:
{
lean_object* v_body_5423_; 
v_body_5423_ = lean_ctor_get(v_x_5422_, 2);
v_x_5422_ = v_body_5423_;
goto _start;
}
case 3:
{
lean_object* v_u_5425_; lean_object* v___x_5426_; 
v_u_5425_ = lean_ctor_get(v_x_5422_, 0);
lean_inc(v_u_5425_);
v___x_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5426_, 0, v_u_5425_);
return v___x_5426_;
}
default: 
{
lean_object* v___x_5427_; 
v___x_5427_ = lean_box(0);
return v___x_5427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_5428_);
lean_dec_ref(v_x_5428_);
return v_res_5429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_5430_, lean_object* v_body_5431_, lean_object* v_x_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_5430_, v_body_5431_, v_x_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_5441_, lean_object* v_xs_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v_l_5449_; 
switch(lean_obj_tag(v_type_5441_))
{
case 3:
{
lean_object* v_u_5452_; 
lean_dec_ref(v_xs_5442_);
v_u_5452_ = lean_ctor_get(v_type_5441_, 0);
lean_inc(v_u_5452_);
lean_dec_ref_known(v_type_5441_, 1);
v_l_5449_ = v_u_5452_;
goto v___jp_5448_;
}
case 7:
{
lean_object* v_binderName_5453_; lean_object* v_binderType_5454_; lean_object* v_body_5455_; uint8_t v_binderInfo_5456_; lean_object* v___f_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; 
v_binderName_5453_ = lean_ctor_get(v_type_5441_, 0);
lean_inc(v_binderName_5453_);
v_binderType_5454_ = lean_ctor_get(v_type_5441_, 1);
lean_inc_ref(v_binderType_5454_);
v_body_5455_ = lean_ctor_get(v_type_5441_, 2);
lean_inc_ref(v_body_5455_);
v_binderInfo_5456_ = lean_ctor_get_uint8(v_type_5441_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_5441_, 3);
lean_inc_ref(v_xs_5442_);
v___f_5457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5457_, 0, v_xs_5442_);
lean_closure_set(v___f_5457_, 1, v_body_5455_);
v___x_5458_ = lean_expr_instantiate_rev(v_binderType_5454_, v_xs_5442_);
lean_dec_ref(v_xs_5442_);
lean_dec_ref(v_binderType_5454_);
v___x_5459_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_5453_, v_binderInfo_5456_, v___x_5458_, v___f_5457_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
return v___x_5459_;
}
default: 
{
lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5460_ = lean_expr_instantiate_rev(v_type_5441_, v_xs_5442_);
lean_dec_ref(v_xs_5442_);
lean_dec_ref(v_type_5441_);
v___x_5461_ = l_Lean_Meta_whnfD(v___x_5460_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5473_; 
v_a_5462_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5464_ = v___x_5461_;
v_isShared_5465_ = v_isSharedCheck_5473_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5461_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5473_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
switch(lean_obj_tag(v_a_5462_))
{
case 3:
{
lean_object* v_u_5466_; 
lean_del_object(v___x_5464_);
v_u_5466_ = lean_ctor_get(v_a_5462_, 0);
lean_inc(v_u_5466_);
lean_dec_ref_known(v_a_5462_, 1);
v_l_5449_ = v_u_5466_;
goto v___jp_5448_;
}
case 7:
{
lean_object* v___x_5467_; 
lean_del_object(v___x_5464_);
v___x_5467_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_5441_ = v_a_5462_;
v_xs_5442_ = v___x_5467_;
goto _start;
}
default: 
{
lean_object* v___x_5469_; lean_object* v___x_5471_; 
lean_dec(v_a_5462_);
v___x_5469_ = lean_box(0);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 0, v___x_5469_);
v___x_5471_ = v___x_5464_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5469_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
}
}
else
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
v_a_5474_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5461_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5461_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
}
v___jp_5448_:
{
lean_object* v___x_5450_; lean_object* v___x_5451_; 
v___x_5450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5450_, 0, v_l_5449_);
v___x_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5451_, 0, v___x_5450_);
return v___x_5451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_5482_, lean_object* v_body_5483_, lean_object* v_x_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_){
_start:
{
lean_object* v___x_5490_; lean_object* v___x_5491_; 
v___x_5490_ = lean_array_push(v_xs_5482_, v_x_5484_);
v___x_5491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_5483_, v___x_5490_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5492_, lean_object* v_xs_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_){
_start:
{
lean_object* v_res_5499_; 
v_res_5499_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5492_, v_xs_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_);
lean_dec(v_a_5497_);
lean_dec_ref(v_a_5496_);
lean_dec(v_a_5495_);
lean_dec_ref(v_a_5494_);
return v_res_5499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5500_, lean_object* v_cache_5501_, lean_object* v_a_x3f_5502_){
_start:
{
lean_object* v___x_5504_; lean_object* v_mctx_5505_; lean_object* v_zetaDeltaFVarIds_5506_; lean_object* v_postponed_5507_; lean_object* v_diag_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5518_; 
v___x_5504_ = lean_st_ref_take(v_a_5500_);
v_mctx_5505_ = lean_ctor_get(v___x_5504_, 0);
v_zetaDeltaFVarIds_5506_ = lean_ctor_get(v___x_5504_, 2);
v_postponed_5507_ = lean_ctor_get(v___x_5504_, 3);
v_diag_5508_ = lean_ctor_get(v___x_5504_, 4);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5518_ == 0)
{
lean_object* v_unused_5519_; 
v_unused_5519_ = lean_ctor_get(v___x_5504_, 1);
lean_dec(v_unused_5519_);
v___x_5510_ = v___x_5504_;
v_isShared_5511_ = v_isSharedCheck_5518_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_diag_5508_);
lean_inc(v_postponed_5507_);
lean_inc(v_zetaDeltaFVarIds_5506_);
lean_inc(v_mctx_5505_);
lean_dec(v___x_5504_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5518_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5512_; lean_object* v___x_5514_; 
v___x_5512_ = lean_box(0);
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 1, v_cache_5501_);
v___x_5514_ = v___x_5510_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_mctx_5505_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v_cache_5501_);
lean_ctor_set(v_reuseFailAlloc_5517_, 2, v_zetaDeltaFVarIds_5506_);
lean_ctor_set(v_reuseFailAlloc_5517_, 3, v_postponed_5507_);
lean_ctor_set(v_reuseFailAlloc_5517_, 4, v_diag_5508_);
v___x_5514_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = lean_st_ref_put(v_a_5500_, v___x_5514_);
v___x_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5516_, 0, v___x_5512_);
return v___x_5516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5520_, lean_object* v_cache_5521_, lean_object* v_a_x3f_5522_, lean_object* v___y_5523_){
_start:
{
lean_object* v_res_5524_; 
v_res_5524_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5520_, v_cache_5521_, v_a_x3f_5522_);
lean_dec(v_a_x3f_5522_);
lean_dec(v_a_5520_);
return v_res_5524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_){
_start:
{
lean_object* v___x_5531_; 
v___x_5531_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5525_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v_cache_5534_; lean_object* v___x_5535_; 
v___x_5532_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5533_ = lean_st_ref_get(v_a_5527_);
v_cache_5534_ = lean_ctor_get(v___x_5533_, 1);
lean_inc_ref(v_cache_5534_);
lean_dec(v___x_5533_);
v___x_5535_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5525_, v___x_5532_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5552_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5538_ = v___x_5535_;
v_isShared_5539_ = v_isSharedCheck_5552_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5552_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
lean_inc(v_a_5536_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set_tag(v___x_5538_, 1);
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5536_);
v___x_5541_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
v___x_5542_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5527_, v_cache_5534_, v___x_5541_);
lean_dec_ref(v___x_5541_);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5542_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; 
v_unused_5550_ = lean_ctor_get(v___x_5542_, 0);
lean_dec(v_unused_5550_);
v___x_5544_ = v___x_5542_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_dec(v___x_5542_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
lean_ctor_set(v___x_5544_, 0, v_a_5536_);
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5536_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
}
else
{
lean_object* v_a_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
v_a_5553_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_a_5553_);
lean_dec_ref_known(v___x_5535_, 1);
v___x_5554_ = lean_box(0);
v___x_5555_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5527_, v_cache_5534_, v___x_5554_);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5555_);
if (v_isSharedCheck_5562_ == 0)
{
lean_object* v_unused_5563_; 
v_unused_5563_ = lean_ctor_get(v___x_5555_, 0);
lean_dec(v_unused_5563_);
v___x_5557_ = v___x_5555_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_dec(v___x_5555_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
lean_ctor_set_tag(v___x_5557_, 1);
lean_ctor_set(v___x_5557_, 0, v_a_5553_);
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5553_);
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
lean_object* v___x_5564_; 
lean_dec_ref(v_type_5525_);
v___x_5564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5531_);
return v___x_5564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_){
_start:
{
lean_object* v_res_5571_; 
v_res_5571_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
return v_res_5571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_){
_start:
{
lean_object* v___x_5578_; 
v___x_5578_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5593_; 
v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5581_ = v___x_5578_;
v_isShared_5582_ = v_isSharedCheck_5593_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5578_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5593_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
if (lean_obj_tag(v_a_5579_) == 0)
{
uint8_t v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5586_; 
v___x_5583_ = 0;
v___x_5584_ = lean_box(v___x_5583_);
if (v_isShared_5582_ == 0)
{
lean_ctor_set(v___x_5581_, 0, v___x_5584_);
v___x_5586_ = v___x_5581_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5584_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
else
{
uint8_t v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5591_; 
lean_dec_ref_known(v_a_5579_, 1);
v___x_5588_ = 1;
v___x_5589_ = lean_box(v___x_5588_);
if (v_isShared_5582_ == 0)
{
lean_ctor_set(v___x_5581_, 0, v___x_5589_);
v___x_5591_ = v___x_5581_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5589_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
}
else
{
lean_object* v_a_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5601_; 
v_a_5594_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5596_ = v___x_5578_;
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5578_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v___x_5599_; 
if (v_isShared_5597_ == 0)
{
v___x_5599_ = v___x_5596_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_a_5594_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
return v___x_5599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_){
_start:
{
lean_object* v_res_5608_; 
v_res_5608_ = l_Lean_Meta_isTypeFormerType(v_type_5602_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_);
lean_dec(v_a_5606_);
lean_dec_ref(v_a_5605_);
lean_dec(v_a_5604_);
lean_dec_ref(v_a_5603_);
return v_res_5608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_){
_start:
{
lean_object* v___x_5615_; 
v___x_5615_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_);
if (lean_obj_tag(v___x_5615_) == 0)
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5631_; 
v_a_5616_ = lean_ctor_get(v___x_5615_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5615_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5618_ = v___x_5615_;
v_isShared_5619_ = v_isSharedCheck_5631_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5615_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5631_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
if (lean_obj_tag(v_a_5616_) == 1)
{
lean_object* v_val_5620_; uint8_t v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5624_; 
v_val_5620_ = lean_ctor_get(v_a_5616_, 0);
lean_inc(v_val_5620_);
lean_dec_ref_known(v_a_5616_, 1);
v___x_5621_ = l_Lean_Level_isAlwaysZero(v_val_5620_);
lean_dec(v_val_5620_);
v___x_5622_ = lean_box(v___x_5621_);
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 0, v___x_5622_);
v___x_5624_ = v___x_5618_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v___x_5622_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
else
{
uint8_t v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5629_; 
lean_dec(v_a_5616_);
v___x_5626_ = 0;
v___x_5627_ = lean_box(v___x_5626_);
if (v_isShared_5619_ == 0)
{
lean_ctor_set(v___x_5618_, 0, v___x_5627_);
v___x_5629_ = v___x_5618_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
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
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
v_a_5632_ = lean_ctor_get(v___x_5615_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5615_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5615_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5615_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l_Lean_Meta_isPropFormerType(v_type_5640_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_);
lean_dec(v_a_5644_);
lean_dec_ref(v_a_5643_);
lean_dec(v_a_5642_);
lean_dec_ref(v_a_5641_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v___x_5653_; 
lean_inc(v_a_5651_);
lean_inc_ref(v_a_5650_);
lean_inc(v_a_5649_);
lean_inc_ref(v_a_5648_);
v___x_5653_ = lean_infer_type(v_e_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; lean_object* v___x_5655_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
lean_inc(v_a_5654_);
lean_dec_ref_known(v___x_5653_, 1);
v___x_5655_ = l_Lean_Meta_isTypeFormerType(v_a_5654_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
return v___x_5655_;
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
v_a_5656_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5653_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5653_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l_Lean_Meta_isTypeFormer(v_e_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
lean_dec(v_a_5668_);
lean_dec_ref(v_a_5667_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5671_, lean_object* v_maxFVars_x3f_5672_, lean_object* v_k_5673_, uint8_t v_cleanupAnnotations_5674_, uint8_t v_whnfType_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_){
_start:
{
lean_object* v___f_5681_; lean_object* v___x_5682_; 
v___f_5681_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5681_, 0, v_k_5673_);
v___x_5682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5671_, v_maxFVars_x3f_5672_, v___f_5681_, v_cleanupAnnotations_5674_, v_whnfType_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5690_; 
v_a_5683_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5685_ = v___x_5682_;
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_dec(v___x_5682_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5686_ == 0)
{
v___x_5688_ = v___x_5685_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5683_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
else
{
lean_object* v_a_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5698_; 
v_a_5691_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5693_ = v___x_5682_;
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_a_5691_);
lean_dec(v___x_5682_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5696_; 
if (v_isShared_5694_ == 0)
{
v___x_5696_ = v___x_5693_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_a_5691_);
v___x_5696_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
return v___x_5696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5699_, lean_object* v_maxFVars_x3f_5700_, lean_object* v_k_5701_, lean_object* v_cleanupAnnotations_5702_, lean_object* v_whnfType_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5709_; uint8_t v_whnfType_boxed_5710_; lean_object* v_res_5711_; 
v_cleanupAnnotations_boxed_5709_ = lean_unbox(v_cleanupAnnotations_5702_);
v_whnfType_boxed_5710_ = lean_unbox(v_whnfType_5703_);
v_res_5711_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5699_, v_maxFVars_x3f_5700_, v_k_5701_, v_cleanupAnnotations_boxed_5709_, v_whnfType_boxed_5710_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_);
lean_dec(v___y_5707_);
lean_dec_ref(v___y_5706_);
lean_dec(v___y_5705_);
lean_dec_ref(v___y_5704_);
return v_res_5711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5712_, lean_object* v_type_5713_, lean_object* v_maxFVars_x3f_5714_, lean_object* v_k_5715_, uint8_t v_cleanupAnnotations_5716_, uint8_t v_whnfType_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
lean_object* v___x_5723_; 
v___x_5723_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5713_, v_maxFVars_x3f_5714_, v_k_5715_, v_cleanupAnnotations_5716_, v_whnfType_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_);
return v___x_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5724_, lean_object* v_type_5725_, lean_object* v_maxFVars_x3f_5726_, lean_object* v_k_5727_, lean_object* v_cleanupAnnotations_5728_, lean_object* v_whnfType_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5735_; uint8_t v_whnfType_boxed_5736_; lean_object* v_res_5737_; 
v_cleanupAnnotations_boxed_5735_ = lean_unbox(v_cleanupAnnotations_5728_);
v_whnfType_boxed_5736_ = lean_unbox(v_whnfType_5729_);
v_res_5737_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5724_, v_type_5725_, v_maxFVars_x3f_5726_, v_k_5727_, v_cleanupAnnotations_boxed_5735_, v_whnfType_boxed_5736_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
return v_res_5737_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5738_, lean_object* v_as_5739_, size_t v_i_5740_, size_t v_stop_5741_){
_start:
{
uint8_t v___x_5742_; 
v___x_5742_ = lean_usize_dec_eq(v_i_5740_, v_stop_5741_);
if (v___x_5742_ == 0)
{
lean_object* v___x_5743_; uint8_t v___x_5744_; 
v___x_5743_ = lean_array_uget_borrowed(v_as_5739_, v_i_5740_);
v___x_5744_ = lean_expr_eqv(v_a_5738_, v___x_5743_);
if (v___x_5744_ == 0)
{
size_t v___x_5745_; size_t v___x_5746_; 
v___x_5745_ = ((size_t)1ULL);
v___x_5746_ = lean_usize_add(v_i_5740_, v___x_5745_);
v_i_5740_ = v___x_5746_;
goto _start;
}
else
{
return v___x_5744_;
}
}
else
{
uint8_t v___x_5748_; 
v___x_5748_ = 0;
return v___x_5748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5749_, lean_object* v_as_5750_, lean_object* v_i_5751_, lean_object* v_stop_5752_){
_start:
{
size_t v_i_boxed_5753_; size_t v_stop_boxed_5754_; uint8_t v_res_5755_; lean_object* v_r_5756_; 
v_i_boxed_5753_ = lean_unbox_usize(v_i_5751_);
lean_dec(v_i_5751_);
v_stop_boxed_5754_ = lean_unbox_usize(v_stop_5752_);
lean_dec(v_stop_5752_);
v_res_5755_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5749_, v_as_5750_, v_i_boxed_5753_, v_stop_boxed_5754_);
lean_dec_ref(v_as_5750_);
lean_dec_ref(v_a_5749_);
v_r_5756_ = lean_box(v_res_5755_);
return v_r_5756_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5757_, lean_object* v_a_5758_){
_start:
{
lean_object* v___x_5759_; lean_object* v___x_5760_; uint8_t v___x_5761_; 
v___x_5759_ = lean_unsigned_to_nat(0u);
v___x_5760_ = lean_array_get_size(v_as_5757_);
v___x_5761_ = lean_nat_dec_lt(v___x_5759_, v___x_5760_);
if (v___x_5761_ == 0)
{
return v___x_5761_;
}
else
{
size_t v___x_5762_; size_t v___x_5763_; uint8_t v___x_5764_; 
v___x_5762_ = ((size_t)0ULL);
v___x_5763_ = lean_usize_of_nat(v___x_5760_);
v___x_5764_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5758_, v_as_5757_, v___x_5762_, v___x_5763_);
return v___x_5764_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5765_, lean_object* v_a_5766_){
_start:
{
uint8_t v_res_5767_; lean_object* v_r_5768_; 
v_res_5767_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5765_, v_a_5766_);
lean_dec_ref(v_a_5766_);
lean_dec_ref(v_as_5765_);
v_r_5768_ = lean_box(v_res_5767_);
return v_r_5768_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5769_, lean_object* v_e_5770_){
_start:
{
uint8_t v___x_5771_; lean_object* v_d_5773_; lean_object* v_b_5774_; 
v___x_5771_ = l_Lean_Expr_hasFVar(v_e_5770_);
if (v___x_5771_ == 0)
{
lean_dec_ref(v_e_5770_);
return v___x_5771_;
}
else
{
switch(lean_obj_tag(v_e_5770_))
{
case 7:
{
lean_object* v_binderType_5777_; lean_object* v_body_5778_; 
v_binderType_5777_ = lean_ctor_get(v_e_5770_, 1);
lean_inc_ref(v_binderType_5777_);
v_body_5778_ = lean_ctor_get(v_e_5770_, 2);
lean_inc_ref(v_body_5778_);
lean_dec_ref_known(v_e_5770_, 3);
v_d_5773_ = v_binderType_5777_;
v_b_5774_ = v_body_5778_;
goto v___jp_5772_;
}
case 6:
{
lean_object* v_binderType_5779_; lean_object* v_body_5780_; 
v_binderType_5779_ = lean_ctor_get(v_e_5770_, 1);
lean_inc_ref(v_binderType_5779_);
v_body_5780_ = lean_ctor_get(v_e_5770_, 2);
lean_inc_ref(v_body_5780_);
lean_dec_ref_known(v_e_5770_, 3);
v_d_5773_ = v_binderType_5779_;
v_b_5774_ = v_body_5780_;
goto v___jp_5772_;
}
case 10:
{
lean_object* v_expr_5781_; 
v_expr_5781_ = lean_ctor_get(v_e_5770_, 1);
lean_inc_ref(v_expr_5781_);
lean_dec_ref_known(v_e_5770_, 2);
v_e_5770_ = v_expr_5781_;
goto _start;
}
case 8:
{
lean_object* v_type_5783_; lean_object* v_value_5784_; lean_object* v_body_5785_; uint8_t v___x_5786_; 
v_type_5783_ = lean_ctor_get(v_e_5770_, 1);
lean_inc_ref(v_type_5783_);
v_value_5784_ = lean_ctor_get(v_e_5770_, 2);
lean_inc_ref(v_value_5784_);
v_body_5785_ = lean_ctor_get(v_e_5770_, 3);
lean_inc_ref(v_body_5785_);
lean_dec_ref_known(v_e_5770_, 4);
v___x_5786_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5769_, v_type_5783_);
if (v___x_5786_ == 0)
{
uint8_t v___x_5787_; 
v___x_5787_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5769_, v_value_5784_);
if (v___x_5787_ == 0)
{
v_e_5770_ = v_body_5785_;
goto _start;
}
else
{
lean_dec_ref(v_body_5785_);
return v___x_5771_;
}
}
else
{
lean_dec_ref(v_body_5785_);
lean_dec_ref(v_value_5784_);
return v___x_5771_;
}
}
case 5:
{
lean_object* v_fn_5789_; lean_object* v_arg_5790_; uint8_t v___x_5791_; 
v_fn_5789_ = lean_ctor_get(v_e_5770_, 0);
lean_inc_ref(v_fn_5789_);
v_arg_5790_ = lean_ctor_get(v_e_5770_, 1);
lean_inc_ref(v_arg_5790_);
lean_dec_ref_known(v_e_5770_, 2);
v___x_5791_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5769_, v_fn_5789_);
if (v___x_5791_ == 0)
{
v_e_5770_ = v_arg_5790_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5790_);
return v___x_5771_;
}
}
case 11:
{
lean_object* v_struct_5793_; 
v_struct_5793_ = lean_ctor_get(v_e_5770_, 2);
lean_inc_ref(v_struct_5793_);
lean_dec_ref_known(v_e_5770_, 3);
v_e_5770_ = v_struct_5793_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5795_; lean_object* v___x_5796_; uint8_t v___x_5797_; 
v_fvarId_5795_ = lean_ctor_get(v_e_5770_, 0);
lean_inc(v_fvarId_5795_);
lean_dec_ref_known(v_e_5770_, 1);
v___x_5796_ = l_Lean_Expr_fvar___override(v_fvarId_5795_);
v___x_5797_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5769_, v___x_5796_);
lean_dec_ref(v___x_5796_);
return v___x_5797_;
}
default: 
{
uint8_t v___x_5798_; 
lean_dec_ref(v_e_5770_);
v___x_5798_ = 0;
return v___x_5798_;
}
}
}
v___jp_5772_:
{
uint8_t v___x_5775_; 
v___x_5775_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5769_, v_d_5773_);
if (v___x_5775_ == 0)
{
v_e_5770_ = v_b_5774_;
goto _start;
}
else
{
lean_dec_ref(v_b_5774_);
return v___x_5771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5799_, lean_object* v_e_5800_){
_start:
{
uint8_t v_res_5801_; lean_object* v_r_5802_; 
v_res_5801_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5799_, v_e_5800_);
lean_dec_ref(v_xs_5799_);
v_r_5802_ = lean_box(v_res_5801_);
return v_r_5802_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5804_; lean_object* v___x_5805_; 
v___x_5804_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5805_ = l_Lean_stringToMessageData(v___x_5804_);
return v___x_5805_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5808_ = l_Lean_stringToMessageData(v___x_5807_);
return v___x_5808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5809_, lean_object* v_type_5810_, lean_object* v_as_5811_, size_t v_sz_5812_, size_t v_i_5813_, lean_object* v_b_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_){
_start:
{
lean_object* v_a_5821_; uint8_t v___x_5825_; 
v___x_5825_ = lean_usize_dec_lt(v_i_5813_, v_sz_5812_);
if (v___x_5825_ == 0)
{
lean_object* v___x_5826_; 
lean_dec_ref(v_type_5810_);
v___x_5826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5826_, 0, v_b_5814_);
return v___x_5826_;
}
else
{
lean_object* v___x_5827_; lean_object* v_a_5828_; uint8_t v___x_5829_; 
v___x_5827_ = lean_box(0);
v_a_5828_ = lean_array_uget_borrowed(v_as_5811_, v_i_5813_);
lean_inc(v_a_5828_);
v___x_5829_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5809_, v_a_5828_);
if (v___x_5829_ == 0)
{
v_a_5821_ = v___x_5827_;
goto v___jp_5820_;
}
else
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; 
v___x_5830_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5828_);
v___x_5831_ = l_Lean_MessageData_ofExpr(v_a_5828_);
v___x_5832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5830_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
v___x_5833_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5832_);
lean_ctor_set(v___x_5834_, 1, v___x_5833_);
lean_inc_ref(v_type_5810_);
v___x_5835_ = l_Lean_MessageData_ofExpr(v_type_5810_);
v___x_5836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5834_);
lean_ctor_set(v___x_5836_, 1, v___x_5835_);
v___x_5837_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5836_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_dec_ref_known(v___x_5837_, 1);
v_a_5821_ = v___x_5827_;
goto v___jp_5820_;
}
else
{
lean_dec_ref(v_type_5810_);
return v___x_5837_;
}
}
}
v___jp_5820_:
{
size_t v___x_5822_; size_t v___x_5823_; 
v___x_5822_ = ((size_t)1ULL);
v___x_5823_ = lean_usize_add(v_i_5813_, v___x_5822_);
v_i_5813_ = v___x_5823_;
v_b_5814_ = v_a_5821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5838_, lean_object* v_type_5839_, lean_object* v_as_5840_, lean_object* v_sz_5841_, lean_object* v_i_5842_, lean_object* v_b_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_){
_start:
{
size_t v_sz_boxed_5849_; size_t v_i_boxed_5850_; lean_object* v_res_5851_; 
v_sz_boxed_5849_ = lean_unbox_usize(v_sz_5841_);
lean_dec(v_sz_5841_);
v_i_boxed_5850_ = lean_unbox_usize(v_i_5842_);
lean_dec(v_i_5842_);
v_res_5851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5838_, v_type_5839_, v_as_5840_, v_sz_boxed_5849_, v_i_boxed_5850_, v_b_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
lean_dec(v___y_5845_);
lean_dec_ref(v___y_5844_);
lean_dec_ref(v_as_5840_);
lean_dec_ref(v_xs_5838_);
return v_res_5851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5852_, size_t v_i_5853_, lean_object* v_bs_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_){
_start:
{
uint8_t v___x_5860_; 
v___x_5860_ = lean_usize_dec_lt(v_i_5853_, v_sz_5852_);
if (v___x_5860_ == 0)
{
lean_object* v___x_5861_; 
v___x_5861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5861_, 0, v_bs_5854_);
return v___x_5861_;
}
else
{
lean_object* v_v_5862_; lean_object* v___x_5863_; lean_object* v_bs_x27_5864_; lean_object* v___x_5865_; 
v_v_5862_ = lean_array_uget(v_bs_5854_, v_i_5853_);
v___x_5863_ = lean_unsigned_to_nat(0u);
v_bs_x27_5864_ = lean_array_uset(v_bs_5854_, v_i_5853_, v___x_5863_);
lean_inc(v___y_5858_);
lean_inc_ref(v___y_5857_);
lean_inc(v___y_5856_);
lean_inc_ref(v___y_5855_);
v___x_5865_ = lean_infer_type(v_v_5862_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_);
if (lean_obj_tag(v___x_5865_) == 0)
{
lean_object* v_a_5866_; size_t v___x_5867_; size_t v___x_5868_; lean_object* v___x_5869_; 
v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
lean_inc(v_a_5866_);
lean_dec_ref_known(v___x_5865_, 1);
v___x_5867_ = ((size_t)1ULL);
v___x_5868_ = lean_usize_add(v_i_5853_, v___x_5867_);
v___x_5869_ = lean_array_uset(v_bs_x27_5864_, v_i_5853_, v_a_5866_);
v_i_5853_ = v___x_5868_;
v_bs_5854_ = v___x_5869_;
goto _start;
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec_ref(v_bs_x27_5864_);
v_a_5871_ = lean_ctor_get(v___x_5865_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5865_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5865_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5865_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5879_, lean_object* v_i_5880_, lean_object* v_bs_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_){
_start:
{
size_t v_sz_boxed_5887_; size_t v_i_boxed_5888_; lean_object* v_res_5889_; 
v_sz_boxed_5887_ = lean_unbox_usize(v_sz_5879_);
lean_dec(v_sz_5879_);
v_i_boxed_5888_ = lean_unbox_usize(v_i_5880_);
lean_dec(v_i_5880_);
v_res_5889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5887_, v_i_boxed_5888_, v_bs_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
lean_dec(v___y_5885_);
lean_dec_ref(v___y_5884_);
lean_dec(v___y_5883_);
lean_dec_ref(v___y_5882_);
return v_res_5889_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___x_5891_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5892_ = l_Lean_stringToMessageData(v___x_5891_);
return v___x_5892_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5894_; lean_object* v___x_5895_; 
v___x_5894_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5895_ = l_Lean_stringToMessageData(v___x_5894_);
return v___x_5895_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; 
v___x_5897_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5898_ = l_Lean_stringToMessageData(v___x_5897_);
return v___x_5898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5899_, lean_object* v_n_5900_, lean_object* v_xs_5901_, lean_object* v_x_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_){
_start:
{
lean_object* v___x_5932_; uint8_t v___x_5933_; 
v___x_5932_ = lean_array_get_size(v_xs_5901_);
v___x_5933_ = lean_nat_dec_eq(v___x_5932_, v_n_5900_);
if (v___x_5933_ == 0)
{
lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v_a_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5953_; 
lean_dec_ref(v_xs_5901_);
v___x_5934_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5935_ = l_Lean_MessageData_ofExpr(v_type_5899_);
v___x_5936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = l_Nat_reprFast(v_n_5900_);
v___x_5940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5939_);
v___x_5941_ = l_Lean_MessageData_ofFormat(v___x_5940_);
v___x_5942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5938_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
v___x_5943_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5944_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
v_a_5946_ = lean_ctor_get(v___x_5945_, 0);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___x_5945_);
if (v_isSharedCheck_5953_ == 0)
{
v___x_5948_ = v___x_5945_;
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_a_5946_);
lean_dec(v___x_5945_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
if (v_isShared_5949_ == 0)
{
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5946_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
}
}
}
else
{
lean_dec(v_n_5900_);
goto v___jp_5908_;
}
v___jp_5908_:
{
size_t v_sz_5909_; size_t v___x_5910_; lean_object* v___x_5911_; 
v_sz_5909_ = lean_array_size(v_xs_5901_);
v___x_5910_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5901_);
v___x_5911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5909_, v___x_5910_, v_xs_5901_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
if (lean_obj_tag(v___x_5911_) == 0)
{
lean_object* v_a_5912_; lean_object* v___x_5913_; size_t v_sz_5914_; lean_object* v___x_5915_; 
v_a_5912_ = lean_ctor_get(v___x_5911_, 0);
lean_inc(v_a_5912_);
lean_dec_ref_known(v___x_5911_, 1);
v___x_5913_ = lean_box(0);
v_sz_5914_ = lean_array_size(v_a_5912_);
v___x_5915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5901_, v_type_5899_, v_a_5912_, v_sz_5914_, v___x_5910_, v___x_5913_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
lean_dec_ref(v_xs_5901_);
if (lean_obj_tag(v___x_5915_) == 0)
{
lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5922_; 
v_isSharedCheck_5922_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_5922_ == 0)
{
lean_object* v_unused_5923_; 
v_unused_5923_ = lean_ctor_get(v___x_5915_, 0);
lean_dec(v_unused_5923_);
v___x_5917_ = v___x_5915_;
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
else
{
lean_dec(v___x_5915_);
v___x_5917_ = lean_box(0);
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
v_resetjp_5916_:
{
lean_object* v___x_5920_; 
if (v_isShared_5918_ == 0)
{
lean_ctor_set(v___x_5917_, 0, v_a_5912_);
v___x_5920_ = v___x_5917_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5921_; 
v_reuseFailAlloc_5921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5921_, 0, v_a_5912_);
v___x_5920_ = v_reuseFailAlloc_5921_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
return v___x_5920_;
}
}
}
else
{
lean_object* v_a_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5931_; 
lean_dec(v_a_5912_);
v_a_5924_ = lean_ctor_get(v___x_5915_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5926_ = v___x_5915_;
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_a_5924_);
lean_dec(v___x_5915_);
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
}
else
{
lean_dec_ref(v_xs_5901_);
lean_dec_ref(v_type_5899_);
return v___x_5911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5954_, lean_object* v_n_5955_, lean_object* v_xs_5956_, lean_object* v_x_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_){
_start:
{
lean_object* v_res_5963_; 
v_res_5963_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5954_, v_n_5955_, v_xs_5956_, v_x_5957_, v___y_5958_, v___y_5959_, v___y_5960_, v___y_5961_);
lean_dec(v___y_5961_);
lean_dec_ref(v___y_5960_);
lean_dec(v___y_5959_);
lean_dec_ref(v___y_5958_);
lean_dec_ref(v_x_5957_);
return v_res_5963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5964_, lean_object* v_type_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_){
_start:
{
lean_object* v___f_5971_; lean_object* v___x_5972_; uint8_t v___x_5973_; lean_object* v___x_5974_; 
lean_inc(v_n_5964_);
lean_inc_ref(v_type_5965_);
v___f_5971_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5971_, 0, v_type_5965_);
lean_closure_set(v___f_5971_, 1, v_n_5964_);
v___x_5972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5972_, 0, v_n_5964_);
v___x_5973_ = 0;
v___x_5974_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5965_, v___x_5972_, v___f_5971_, v___x_5973_, v___x_5973_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
return v___x_5974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5975_, lean_object* v_type_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_){
_start:
{
lean_object* v_res_5982_; 
v_res_5982_ = l_Lean_Meta_arrowDomainsN(v_n_5975_, v_type_5976_, v_a_5977_, v_a_5978_, v_a_5979_, v_a_5980_);
lean_dec(v_a_5980_);
lean_dec_ref(v_a_5979_);
lean_dec(v_a_5978_);
lean_dec_ref(v_a_5977_);
return v_res_5982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5983_, lean_object* v_e_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_){
_start:
{
lean_object* v___x_5990_; 
lean_inc(v_a_5988_);
lean_inc_ref(v_a_5987_);
lean_inc(v_a_5986_);
lean_inc_ref(v_a_5985_);
v___x_5990_ = lean_infer_type(v_e_5984_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_);
if (lean_obj_tag(v___x_5990_) == 0)
{
lean_object* v_a_5991_; lean_object* v___x_5992_; 
v_a_5991_ = lean_ctor_get(v___x_5990_, 0);
lean_inc(v_a_5991_);
lean_dec_ref_known(v___x_5990_, 1);
v___x_5992_ = l_Lean_Meta_arrowDomainsN(v_n_5983_, v_a_5991_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_);
return v___x_5992_;
}
else
{
lean_object* v_a_5993_; lean_object* v___x_5995_; uint8_t v_isShared_5996_; uint8_t v_isSharedCheck_6000_; 
lean_dec(v_n_5983_);
v_a_5993_ = lean_ctor_get(v___x_5990_, 0);
v_isSharedCheck_6000_ = !lean_is_exclusive(v___x_5990_);
if (v_isSharedCheck_6000_ == 0)
{
v___x_5995_ = v___x_5990_;
v_isShared_5996_ = v_isSharedCheck_6000_;
goto v_resetjp_5994_;
}
else
{
lean_inc(v_a_5993_);
lean_dec(v___x_5990_);
v___x_5995_ = lean_box(0);
v_isShared_5996_ = v_isSharedCheck_6000_;
goto v_resetjp_5994_;
}
v_resetjp_5994_:
{
lean_object* v___x_5998_; 
if (v_isShared_5996_ == 0)
{
v___x_5998_ = v___x_5995_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_5999_; 
v_reuseFailAlloc_5999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5993_);
v___x_5998_ = v_reuseFailAlloc_5999_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
return v___x_5998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_6001_, lean_object* v_e_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_){
_start:
{
lean_object* v_res_6008_; 
v_res_6008_ = l_Lean_Meta_inferArgumentTypesN(v_n_6001_, v_e_6002_, v_a_6003_, v_a_6004_, v_a_6005_, v_a_6006_);
lean_dec(v_a_6006_);
lean_dec_ref(v_a_6005_);
lean_dec(v_a_6004_);
lean_dec_ref(v_a_6003_);
return v_res_6008_;
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
