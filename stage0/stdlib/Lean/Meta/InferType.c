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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_309_ = lean_unsigned_to_nat(1864u);
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
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1326_, lean_object* v_idx_1327_, lean_object* v_e_1328_, lean_object* v_a_1329_, lean_object* v_00_u03b1_1330_, lean_object* v_x_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1337_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1338_ = l_Lean_mkProj(v_structName_1326_, v_idx_1327_, v_e_1328_);
v___x_1339_ = l_Lean_indentExpr(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1337_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_indentExpr(v_a_1329_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1344_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1346_, lean_object* v_idx_1347_, lean_object* v_e_1348_, lean_object* v_a_1349_, lean_object* v_00_u03b1_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1346_, v_idx_1347_, v_e_1348_, v_a_1349_, v_00_u03b1_1350_, v_x_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_env_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1364_ = lean_st_ref_get(v___y_1362_);
v_env_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_ref(v_env_1365_);
lean_dec(v___x_1364_);
v___x_1366_ = 0;
lean_inc(v_constName_1358_);
v___x_1367_ = l_Lean_Environment_find_x3f(v_env_1365_, v_constName_1358_, v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1368_;
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_constName_1358_);
v_val_1369_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1367_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_val_1369_);
lean_dec(v___x_1367_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 0);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_val_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1384_, lean_object* v_structName_1385_, lean_object* v_e_1386_, lean_object* v_idx_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_a_1397_; uint8_t v___x_1401_; 
v___x_1401_ = lean_nat_dec_lt(v_a_1389_, v_upperBound_1384_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_idx_1387_);
lean_dec_ref(v_e_1386_);
lean_dec(v_structName_1385_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_b_1390_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; 
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
v___x_1403_ = lean_whnf(v_b_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
if (lean_obj_tag(v_a_1404_) == 7)
{
lean_object* v_body_1405_; uint8_t v___x_1406_; 
v_body_1405_ = lean_ctor_get(v_a_1404_, 2);
lean_inc_ref(v_body_1405_);
lean_dec_ref_known(v_a_1404_, 3);
v___x_1406_ = l_Lean_Expr_hasLooseBVars(v_body_1405_);
if (v___x_1406_ == 0)
{
v_a_1397_ = v_body_1405_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_inc_ref(v_e_1386_);
lean_inc(v_a_1389_);
lean_inc(v_structName_1385_);
v___x_1407_ = l_Lean_mkProj(v_structName_1385_, v_a_1389_, v_e_1386_);
v___x_1408_ = lean_expr_instantiate1(v_body_1405_, v___x_1407_);
lean_dec_ref(v___x_1407_);
lean_dec_ref(v_body_1405_);
v_a_1397_ = v___x_1408_;
goto v___jp_1396_;
}
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1386_);
lean_inc(v_idx_1387_);
lean_inc(v_structName_1385_);
v___x_1410_ = l_Lean_mkProj(v_structName_1385_, v_idx_1387_, v_e_1386_);
v___x_1411_ = l_Lean_indentExpr(v___x_1410_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1409_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
lean_inc_ref(v_a_1388_);
v___x_1415_ = l_Lean_indentExpr(v_a_1388_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1416_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v_a_1397_ = v_a_1404_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_a_1404_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_idx_1387_);
lean_dec_ref(v_e_1386_);
lean_dec(v_structName_1385_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
else
{
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_idx_1387_);
lean_dec_ref(v_e_1386_);
lean_dec(v_structName_1385_);
return v___x_1403_;
}
}
v___jp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v_a_1389_, v___x_1398_);
lean_dec(v_a_1389_);
v_a_1389_ = v___x_1399_;
v_b_1390_ = v_a_1397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1426_, lean_object* v_structName_1427_, lean_object* v_e_1428_, lean_object* v_idx_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1426_, v_structName_1427_, v_e_1428_, v_idx_1429_, v_a_1430_, v_a_1431_, v_b_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_upperBound_1426_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1439_, lean_object* v_structName_1440_, lean_object* v_e_1441_, lean_object* v_idx_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_a_1452_; uint8_t v___x_1456_; 
v___x_1456_ = lean_nat_dec_lt(v_a_1444_, v_upperBound_1439_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_idx_1442_);
lean_dec_ref(v_e_1441_);
lean_dec(v_structName_1440_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_b_1445_);
return v___x_1457_;
}
else
{
lean_object* v___x_1458_; 
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
v___x_1458_ = lean_whnf(v_b_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
if (lean_obj_tag(v_a_1459_) == 7)
{
lean_object* v_body_1460_; uint8_t v___x_1461_; 
v_body_1460_ = lean_ctor_get(v_a_1459_, 2);
lean_inc_ref(v_body_1460_);
lean_dec_ref_known(v_a_1459_, 3);
v___x_1461_ = l_Lean_Expr_hasLooseBVars(v_body_1460_);
if (v___x_1461_ == 0)
{
v_a_1452_ = v_body_1460_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_inc_ref(v_e_1441_);
lean_inc(v_a_1444_);
lean_inc(v_structName_1440_);
v___x_1462_ = l_Lean_mkProj(v_structName_1440_, v_a_1444_, v_e_1441_);
v___x_1463_ = lean_expr_instantiate1(v_body_1460_, v___x_1462_);
lean_dec_ref(v___x_1462_);
lean_dec_ref(v_body_1460_);
v_a_1452_ = v___x_1463_;
goto v___jp_1451_;
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1464_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1441_);
lean_inc(v_idx_1442_);
lean_inc(v_structName_1440_);
v___x_1465_ = l_Lean_mkProj(v_structName_1440_, v_idx_1442_, v_e_1441_);
v___x_1466_ = l_Lean_indentExpr(v___x_1465_);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1464_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
lean_inc_ref(v_a_1443_);
v___x_1470_ = l_Lean_indentExpr(v_a_1443_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1471_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_dec_ref_known(v___x_1472_, 1);
v_a_1452_ = v_a_1459_;
goto v___jp_1451_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1459_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_idx_1442_);
lean_dec_ref(v_e_1441_);
lean_dec(v_structName_1440_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
else
{
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_idx_1442_);
lean_dec_ref(v_e_1441_);
lean_dec(v_structName_1440_);
return v___x_1458_;
}
}
v___jp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_add(v_a_1444_, v___x_1453_);
lean_dec(v_a_1444_);
v___x_1455_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1439_, v_structName_1440_, v_e_1441_, v_idx_1442_, v_a_1443_, v___x_1454_, v_a_1452_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1481_, lean_object* v_structName_1482_, lean_object* v_e_1483_, lean_object* v_idx_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_b_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1481_, v_structName_1482_, v_e_1483_, v_idx_1484_, v_a_1485_, v_a_1486_, v_b_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v_upperBound_1481_);
return v_res_1493_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1494_; lean_object* v_dummy_1495_; 
v___x_1494_ = lean_box(0);
v_dummy_1495_ = l_Lean_Expr_sort___override(v___x_1494_);
return v_dummy_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1496_, lean_object* v_idx_1497_, lean_object* v_e_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; 
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
lean_inc(v_a_1500_);
lean_inc_ref(v_a_1499_);
lean_inc_ref(v_e_1498_);
v___x_1504_ = lean_infer_type(v_e_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
lean_inc(v_a_1500_);
lean_inc_ref(v_a_1499_);
v___x_1506_ = lean_whnf(v_a_1505_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1508_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = l_Lean_Expr_getAppFn(v_a_1507_);
if (lean_obj_tag(v___x_1508_) == 4)
{
lean_object* v_declName_1509_; lean_object* v_us_1510_; lean_object* v___x_1511_; lean_object* v_env_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; 
v_declName_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_declName_1509_);
v_us_1510_ = lean_ctor_get(v___x_1508_, 1);
lean_inc(v_us_1510_);
lean_dec_ref_known(v___x_1508_, 2);
v___x_1511_ = lean_st_ref_get(v_a_1502_);
v_env_1515_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_ref(v_env_1515_);
lean_dec(v___x_1511_);
v___x_1516_ = 0;
v___x_1517_ = l_Lean_Environment_find_x3f(v_env_1515_, v_declName_1509_, v___x_1516_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_us_1510_);
v___x_1518_ = lean_box(0);
v___x_1519_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1518_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1519_;
}
else
{
lean_object* v_val_1520_; 
v_val_1520_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1517_, 1);
if (lean_obj_tag(v_val_1520_) == 5)
{
lean_object* v_val_1521_; lean_object* v_ctors_1522_; 
v_val_1521_ = lean_ctor_get(v_val_1520_, 0);
lean_inc_ref(v_val_1521_);
lean_dec_ref_known(v_val_1520_, 1);
v_ctors_1522_ = lean_ctor_get(v_val_1521_, 4);
lean_inc(v_ctors_1522_);
if (lean_obj_tag(v_ctors_1522_) == 1)
{
lean_object* v_tail_1523_; 
v_tail_1523_ = lean_ctor_get(v_ctors_1522_, 1);
if (lean_obj_tag(v_tail_1523_) == 0)
{
lean_object* v_toConstantVal_1524_; lean_object* v_numParams_1525_; lean_object* v_numIndices_1526_; lean_object* v_head_1527_; lean_object* v___x_1528_; 
v_toConstantVal_1524_ = lean_ctor_get(v_val_1521_, 0);
lean_inc_ref(v_toConstantVal_1524_);
v_numParams_1525_ = lean_ctor_get(v_val_1521_, 1);
lean_inc(v_numParams_1525_);
v_numIndices_1526_ = lean_ctor_get(v_val_1521_, 2);
lean_inc(v_numIndices_1526_);
lean_dec_ref(v_val_1521_);
v_head_1527_ = lean_ctor_get(v_ctors_1522_, 0);
lean_inc(v_head_1527_);
lean_dec_ref_known(v_ctors_1522_, 2);
v___x_1528_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1527_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
if (lean_obj_tag(v_a_1529_) == 6)
{
lean_object* v_val_1530_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v_name_1570_; uint8_t v___x_1571_; 
v_val_1530_ = lean_ctor_get(v_a_1529_, 0);
lean_inc_ref(v_val_1530_);
lean_dec_ref_known(v_a_1529_, 1);
v_name_1570_ = lean_ctor_get(v_toConstantVal_1524_, 0);
lean_inc(v_name_1570_);
lean_dec_ref(v_toConstantVal_1524_);
v___x_1571_ = lean_name_eq(v_name_1570_, v_structName_1496_);
lean_dec(v_name_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_val_1530_);
lean_dec(v_numIndices_1526_);
lean_dec(v_numParams_1525_);
lean_dec(v_us_1510_);
v___x_1572_ = lean_box(0);
v___x_1573_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1572_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
else
{
v___y_1532_ = v_a_1499_;
v___y_1533_ = v_a_1500_;
v___y_1534_ = v_a_1501_;
v___y_1535_ = v_a_1502_;
goto v___jp_1531_;
}
v___jp_1531_:
{
lean_object* v_dummy_1536_; lean_object* v_nargs_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_dummy_1536_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1537_ = l_Lean_Expr_getAppNumArgs(v_a_1507_);
lean_inc(v_nargs_1537_);
v___x_1538_ = lean_mk_array(v_nargs_1537_, v_dummy_1536_);
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_sub(v_nargs_1537_, v___x_1539_);
lean_dec(v_nargs_1537_);
lean_inc(v_a_1507_);
v___x_1541_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1507_, v___x_1538_, v___x_1540_);
v___x_1542_ = lean_nat_add(v_numParams_1525_, v_numIndices_1526_);
lean_dec(v_numIndices_1526_);
v___x_1543_ = lean_array_get_size(v___x_1541_);
v___x_1544_ = lean_nat_dec_eq(v___x_1542_, v___x_1543_);
lean_dec(v___x_1542_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_val_1530_);
lean_dec(v_numParams_1525_);
lean_dec(v_us_1510_);
v___x_1545_ = lean_box(0);
v___x_1546_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1545_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
return v___x_1546_;
}
else
{
lean_object* v_toConstantVal_1547_; lean_object* v_name_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_toConstantVal_1547_ = lean_ctor_get(v_val_1530_, 0);
lean_inc_ref(v_toConstantVal_1547_);
lean_dec_ref(v_val_1530_);
v_name_1548_ = lean_ctor_get(v_toConstantVal_1547_, 0);
lean_inc(v_name_1548_);
lean_dec_ref(v_toConstantVal_1547_);
v___x_1549_ = l_Lean_mkConst(v_name_1548_, v_us_1510_);
v___x_1550_ = lean_unsigned_to_nat(0u);
v___x_1551_ = l_Array_toSubarray___redArg(v___x_1541_, v___x_1550_, v_numParams_1525_);
v___x_1552_ = l_Subarray_copy___redArg(v___x_1551_);
v___x_1553_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1549_, v___x_1552_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
lean_inc(v_a_1507_);
lean_inc_ref(v_e_1498_);
lean_inc(v_structName_1496_);
lean_inc(v_idx_1497_);
v___x_1555_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1497_, v_structName_1496_, v_e_1498_, v_idx_1497_, v_a_1507_, v___x_1550_, v_a_1554_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
v___x_1557_ = lean_whnf(v_a_1556_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1569_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1569_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1569_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
if (lean_obj_tag(v_a_1558_) == 7)
{
lean_object* v_binderType_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
lean_dec(v_a_1507_);
lean_dec_ref(v_e_1498_);
lean_dec(v_idx_1497_);
lean_dec(v_structName_1496_);
v_binderType_1562_ = lean_ctor_get(v_a_1558_, 1);
lean_inc_ref(v_binderType_1562_);
lean_dec_ref_known(v_a_1558_, 3);
v___x_1563_ = lean_expr_consume_type_annotations(v_binderType_1562_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1563_);
v___x_1565_ = v___x_1560_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_del_object(v___x_1560_);
lean_dec(v_a_1558_);
v___x_1567_ = lean_box(0);
v___x_1568_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1567_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
return v___x_1568_;
}
}
}
else
{
lean_dec(v_a_1507_);
lean_dec_ref(v_e_1498_);
lean_dec(v_idx_1497_);
lean_dec(v_structName_1496_);
return v___x_1557_;
}
}
else
{
lean_dec(v_a_1507_);
lean_dec_ref(v_e_1498_);
lean_dec(v_idx_1497_);
lean_dec(v_structName_1496_);
return v___x_1555_;
}
}
else
{
lean_dec(v_a_1507_);
lean_dec_ref(v_e_1498_);
lean_dec(v_idx_1497_);
lean_dec(v_structName_1496_);
return v___x_1553_;
}
}
}
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_a_1529_);
lean_dec(v_numIndices_1526_);
lean_dec(v_numParams_1525_);
lean_dec_ref(v_toConstantVal_1524_);
lean_dec(v_us_1510_);
v___x_1582_ = lean_box(0);
v___x_1583_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1582_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1583_;
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v_numIndices_1526_);
lean_dec(v_numParams_1525_);
lean_dec_ref(v_toConstantVal_1524_);
lean_dec(v_us_1510_);
lean_dec(v_a_1507_);
lean_dec_ref(v_e_1498_);
lean_dec(v_idx_1497_);
lean_dec(v_structName_1496_);
v_a_1584_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1528_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1528_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1522_, 2);
lean_dec_ref(v_val_1521_);
lean_dec(v_us_1510_);
goto v___jp_1512_;
}
}
else
{
lean_dec(v_ctors_1522_);
lean_dec_ref(v_val_1521_);
lean_dec(v_us_1510_);
goto v___jp_1512_;
}
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec(v_val_1520_);
lean_dec(v_us_1510_);
v___x_1592_ = lean_box(0);
v___x_1593_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1592_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1593_;
}
}
v___jp_1512_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1513_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1514_;
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v___x_1508_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1496_, v_idx_1497_, v_e_1498_, v_a_1507_, lean_box(0), v___x_1594_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1595_;
}
}
else
{
lean_dec_ref(v_e_1498_);
lean_dec(v_idx_1497_);
lean_dec(v_structName_1496_);
return v___x_1506_;
}
}
else
{
lean_dec_ref(v_e_1498_);
lean_dec(v_idx_1497_);
lean_dec(v_structName_1496_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1596_, lean_object* v_idx_1597_, lean_object* v_e_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1596_, v_idx_1597_, v_e_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1605_, lean_object* v_structName_1606_, lean_object* v_e_1607_, lean_object* v_idx_1608_, lean_object* v_a_1609_, lean_object* v_inst_1610_, lean_object* v_R_1611_, lean_object* v_a_1612_, lean_object* v_b_1613_, lean_object* v_c_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1605_, v_structName_1606_, v_e_1607_, v_idx_1608_, v_a_1609_, v_a_1612_, v_b_1613_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1621_, lean_object* v_structName_1622_, lean_object* v_e_1623_, lean_object* v_idx_1624_, lean_object* v_a_1625_, lean_object* v_inst_1626_, lean_object* v_R_1627_, lean_object* v_a_1628_, lean_object* v_b_1629_, lean_object* v_c_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1621_, v_structName_1622_, v_e_1623_, v_idx_1624_, v_a_1625_, v_inst_1626_, v_R_1627_, v_a_1628_, v_b_1629_, v_c_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v_upperBound_1621_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1637_, lean_object* v_structName_1638_, lean_object* v_e_1639_, lean_object* v_idx_1640_, lean_object* v_a_1641_, lean_object* v_inst_1642_, lean_object* v_R_1643_, lean_object* v_a_1644_, lean_object* v_b_1645_, lean_object* v_c_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1637_, v_structName_1638_, v_e_1639_, v_idx_1640_, v_a_1641_, v_a_1644_, v_b_1645_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1653_, lean_object* v_structName_1654_, lean_object* v_e_1655_, lean_object* v_idx_1656_, lean_object* v_a_1657_, lean_object* v_inst_1658_, lean_object* v_R_1659_, lean_object* v_a_1660_, lean_object* v_b_1661_, lean_object* v_c_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1653_, v_structName_1654_, v_e_1655_, v_idx_1656_, v_a_1657_, v_inst_1658_, v_R_1659_, v_a_1660_, v_b_1661_, v_c_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v_upperBound_1653_);
return v_res_1668_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1678_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1679_ = l_Lean_indentExpr(v_type_1672_);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1680_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1689_, lean_object* v_type_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1697_, lean_object* v_type_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1697_, v_type_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v_ks_1709_; lean_object* v_vs_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1734_; 
v_ks_1709_ = lean_ctor_get(v_x_1705_, 0);
v_vs_1710_ = lean_ctor_get(v_x_1705_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x_1705_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1712_ = v_x_1705_;
v_isShared_1713_ = v_isSharedCheck_1734_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_vs_1710_);
lean_inc(v_ks_1709_);
lean_dec(v_x_1705_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1734_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = lean_array_get_size(v_ks_1709_);
v___x_1715_ = lean_nat_dec_lt(v_x_1706_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_dec(v_x_1706_);
v___x_1716_ = lean_array_push(v_ks_1709_, v_x_1707_);
v___x_1717_ = lean_array_push(v_vs_1710_, v_x_1708_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1717_);
lean_ctor_set(v___x_1712_, 0, v___x_1716_);
v___x_1719_ = v___x_1712_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v_k_x27_1721_; uint8_t v___x_1722_; 
v_k_x27_1721_ = lean_array_fget_borrowed(v_ks_1709_, v_x_1706_);
v___x_1722_ = l_Lean_instBEqMVarId_beq(v_x_1707_, v_k_x27_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1724_; 
if (v_isShared_1713_ == 0)
{
v___x_1724_ = v___x_1712_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_ks_1709_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_vs_1710_);
v___x_1724_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_unsigned_to_nat(1u);
v___x_1726_ = lean_nat_add(v_x_1706_, v___x_1725_);
lean_dec(v_x_1706_);
v_x_1705_ = v___x_1724_;
v_x_1706_ = v___x_1726_;
goto _start;
}
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1729_ = lean_array_fset(v_ks_1709_, v_x_1706_, v_x_1707_);
v___x_1730_ = lean_array_fset(v_vs_1710_, v_x_1706_, v_x_1708_);
lean_dec(v_x_1706_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1730_);
lean_ctor_set(v___x_1712_, 0, v___x_1729_);
v___x_1732_ = v___x_1712_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1735_, lean_object* v_k_1736_, lean_object* v_v_1737_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1735_, v___x_1738_, v_k_1736_, v_v_1737_);
return v___x_1739_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1741_, size_t v_x_1742_, size_t v_x_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
if (lean_obj_tag(v_x_1741_) == 0)
{
lean_object* v_es_1746_; size_t v___x_1747_; size_t v___x_1748_; lean_object* v_j_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_es_1746_ = lean_ctor_get(v_x_1741_, 0);
v___x_1747_ = ((size_t)31ULL);
v___x_1748_ = lean_usize_land(v_x_1742_, v___x_1747_);
v_j_1749_ = lean_usize_to_nat(v___x_1748_);
v___x_1750_ = lean_array_get_size(v_es_1746_);
v___x_1751_ = lean_nat_dec_lt(v_j_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_dec(v_j_1749_);
lean_dec(v_x_1745_);
lean_dec(v_x_1744_);
return v_x_1741_;
}
else
{
lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1790_; 
lean_inc_ref(v_es_1746_);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_x_1741_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_x_1741_, 0);
lean_dec(v_unused_1791_);
v___x_1753_ = v_x_1741_;
v_isShared_1754_ = v_isSharedCheck_1790_;
goto v_resetjp_1752_;
}
else
{
lean_dec(v_x_1741_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1790_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_v_1755_; lean_object* v___x_1756_; lean_object* v_xs_x27_1757_; lean_object* v___y_1759_; 
v_v_1755_ = lean_array_fget(v_es_1746_, v_j_1749_);
v___x_1756_ = lean_box(0);
v_xs_x27_1757_ = lean_array_fset(v_es_1746_, v_j_1749_, v___x_1756_);
switch(lean_obj_tag(v_v_1755_))
{
case 0:
{
lean_object* v_key_1764_; lean_object* v_val_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1775_; 
v_key_1764_ = lean_ctor_get(v_v_1755_, 0);
v_val_1765_ = lean_ctor_get(v_v_1755_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_v_1755_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1767_ = v_v_1755_;
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_val_1765_);
lean_inc(v_key_1764_);
lean_dec(v_v_1755_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Lean_instBEqMVarId_beq(v_x_1744_, v_key_1764_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_del_object(v___x_1767_);
v___x_1770_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1764_, v_val_1765_, v_x_1744_, v_x_1745_);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
v___y_1759_ = v___x_1771_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1773_; 
lean_dec(v_val_1765_);
lean_dec(v_key_1764_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v_x_1745_);
lean_ctor_set(v___x_1767_, 0, v_x_1744_);
v___x_1773_ = v___x_1767_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_x_1744_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_x_1745_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
v___y_1759_ = v___x_1773_;
goto v___jp_1758_;
}
}
}
}
case 1:
{
lean_object* v_node_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1788_; 
v_node_1776_ = lean_ctor_get(v_v_1755_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_v_1755_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1778_ = v_v_1755_;
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_node_1776_);
lean_dec(v_v_1755_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1788_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
size_t v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1780_ = ((size_t)5ULL);
v___x_1781_ = lean_usize_shift_right(v_x_1742_, v___x_1780_);
v___x_1782_ = ((size_t)1ULL);
v___x_1783_ = lean_usize_add(v_x_1743_, v___x_1782_);
v___x_1784_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1776_, v___x_1781_, v___x_1783_, v_x_1744_, v_x_1745_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1784_);
v___x_1786_ = v___x_1778_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
v___y_1759_ = v___x_1786_;
goto v___jp_1758_;
}
}
}
default: 
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_x_1744_);
lean_ctor_set(v___x_1789_, 1, v_x_1745_);
v___y_1759_ = v___x_1789_;
goto v___jp_1758_;
}
}
v___jp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = lean_array_fset(v_xs_x27_1757_, v_j_1749_, v___y_1759_);
lean_dec(v_j_1749_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1760_);
v___x_1762_ = v___x_1753_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
else
{
lean_object* v_ks_1792_; lean_object* v_vs_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1811_; 
v_ks_1792_ = lean_ctor_get(v_x_1741_, 0);
v_vs_1793_ = lean_ctor_get(v_x_1741_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_x_1741_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1795_ = v_x_1741_;
v_isShared_1796_ = v_isSharedCheck_1811_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_vs_1793_);
lean_inc(v_ks_1792_);
lean_dec(v_x_1741_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1811_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_ks_1792_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_vs_1793_);
v___x_1798_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v_newNode_1799_; size_t v___x_1800_; uint8_t v___x_1801_; 
v_newNode_1799_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1798_, v_x_1744_, v_x_1745_);
v___x_1800_ = ((size_t)7ULL);
v___x_1801_ = lean_usize_dec_le(v___x_1800_, v_x_1743_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1802_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1799_);
v___x_1803_ = lean_unsigned_to_nat(4u);
v___x_1804_ = lean_nat_dec_lt(v___x_1802_, v___x_1803_);
lean_dec(v___x_1802_);
if (v___x_1804_ == 0)
{
lean_object* v_ks_1805_; lean_object* v_vs_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_ks_1805_ = lean_ctor_get(v_newNode_1799_, 0);
lean_inc_ref(v_ks_1805_);
v_vs_1806_ = lean_ctor_get(v_newNode_1799_, 1);
lean_inc_ref(v_vs_1806_);
lean_dec_ref(v_newNode_1799_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1743_, v_ks_1805_, v_vs_1806_, v___x_1807_, v___x_1808_);
lean_dec_ref(v_vs_1806_);
lean_dec_ref(v_ks_1805_);
return v___x_1809_;
}
else
{
return v_newNode_1799_;
}
}
else
{
return v_newNode_1799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1812_, lean_object* v_keys_1813_, lean_object* v_vals_1814_, lean_object* v_i_1815_, lean_object* v_entries_1816_){
_start:
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = lean_array_get_size(v_keys_1813_);
v___x_1818_ = lean_nat_dec_lt(v_i_1815_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_dec(v_i_1815_);
return v_entries_1816_;
}
else
{
lean_object* v_k_1819_; lean_object* v_v_1820_; uint64_t v___x_1821_; size_t v_h_1822_; size_t v___x_1823_; lean_object* v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; size_t v_h_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_k_1819_ = lean_array_fget_borrowed(v_keys_1813_, v_i_1815_);
v_v_1820_ = lean_array_fget_borrowed(v_vals_1814_, v_i_1815_);
v___x_1821_ = l_Lean_instHashableMVarId_hash(v_k_1819_);
v_h_1822_ = lean_uint64_to_usize(v___x_1821_);
v___x_1823_ = ((size_t)5ULL);
v___x_1824_ = lean_unsigned_to_nat(1u);
v___x_1825_ = ((size_t)1ULL);
v___x_1826_ = lean_usize_sub(v_depth_1812_, v___x_1825_);
v___x_1827_ = lean_usize_mul(v___x_1823_, v___x_1826_);
v_h_1828_ = lean_usize_shift_right(v_h_1822_, v___x_1827_);
v___x_1829_ = lean_nat_add(v_i_1815_, v___x_1824_);
lean_dec(v_i_1815_);
lean_inc(v_v_1820_);
lean_inc(v_k_1819_);
v___x_1830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1816_, v_h_1828_, v_depth_1812_, v_k_1819_, v_v_1820_);
v_i_1815_ = v___x_1829_;
v_entries_1816_ = v___x_1830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1832_, lean_object* v_keys_1833_, lean_object* v_vals_1834_, lean_object* v_i_1835_, lean_object* v_entries_1836_){
_start:
{
size_t v_depth_boxed_1837_; lean_object* v_res_1838_; 
v_depth_boxed_1837_ = lean_unbox_usize(v_depth_1832_);
lean_dec(v_depth_1832_);
v_res_1838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1837_, v_keys_1833_, v_vals_1834_, v_i_1835_, v_entries_1836_);
lean_dec_ref(v_vals_1834_);
lean_dec_ref(v_keys_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
size_t v_x_1155__boxed_1844_; size_t v_x_1156__boxed_1845_; lean_object* v_res_1846_; 
v_x_1155__boxed_1844_ = lean_unbox_usize(v_x_1840_);
lean_dec(v_x_1840_);
v_x_1156__boxed_1845_ = lean_unbox_usize(v_x_1841_);
lean_dec(v_x_1841_);
v_res_1846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1839_, v_x_1155__boxed_1844_, v_x_1156__boxed_1845_, v_x_1842_, v_x_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
uint64_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v___x_1850_ = l_Lean_instHashableMVarId_hash(v_x_1848_);
v___x_1851_ = lean_uint64_to_usize(v___x_1850_);
v___x_1852_ = ((size_t)1ULL);
v___x_1853_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1847_, v___x_1851_, v___x_1852_, v_x_1848_, v_x_1849_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1854_, lean_object* v_val_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; lean_object* v_mctx_1859_; lean_object* v_cache_1860_; lean_object* v_zetaDeltaFVarIds_1861_; lean_object* v_postponed_1862_; lean_object* v_diag_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1893_; 
v___x_1858_ = lean_st_ref_take(v___y_1856_);
v_mctx_1859_ = lean_ctor_get(v___x_1858_, 0);
v_cache_1860_ = lean_ctor_get(v___x_1858_, 1);
v_zetaDeltaFVarIds_1861_ = lean_ctor_get(v___x_1858_, 2);
v_postponed_1862_ = lean_ctor_get(v___x_1858_, 3);
v_diag_1863_ = lean_ctor_get(v___x_1858_, 4);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1865_ = v___x_1858_;
v_isShared_1866_ = v_isSharedCheck_1893_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_diag_1863_);
lean_inc(v_postponed_1862_);
lean_inc(v_zetaDeltaFVarIds_1861_);
lean_inc(v_cache_1860_);
lean_inc(v_mctx_1859_);
lean_dec(v___x_1858_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1893_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_depth_1867_; lean_object* v_levelAssignDepth_1868_; lean_object* v_lmvarCounter_1869_; lean_object* v_mvarCounter_1870_; lean_object* v_lDecls_1871_; lean_object* v_decls_1872_; lean_object* v_userNames_1873_; lean_object* v_lAssignment_1874_; lean_object* v_eAssignment_1875_; lean_object* v_dAssignment_1876_; lean_object* v_instanceTypedMVars_1877_; lean_object* v_synthNormMemo_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1892_; 
v_depth_1867_ = lean_ctor_get(v_mctx_1859_, 0);
v_levelAssignDepth_1868_ = lean_ctor_get(v_mctx_1859_, 1);
v_lmvarCounter_1869_ = lean_ctor_get(v_mctx_1859_, 2);
v_mvarCounter_1870_ = lean_ctor_get(v_mctx_1859_, 3);
v_lDecls_1871_ = lean_ctor_get(v_mctx_1859_, 4);
v_decls_1872_ = lean_ctor_get(v_mctx_1859_, 5);
v_userNames_1873_ = lean_ctor_get(v_mctx_1859_, 6);
v_lAssignment_1874_ = lean_ctor_get(v_mctx_1859_, 7);
v_eAssignment_1875_ = lean_ctor_get(v_mctx_1859_, 8);
v_dAssignment_1876_ = lean_ctor_get(v_mctx_1859_, 9);
v_instanceTypedMVars_1877_ = lean_ctor_get(v_mctx_1859_, 10);
v_synthNormMemo_1878_ = lean_ctor_get(v_mctx_1859_, 11);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_mctx_1859_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1880_ = v_mctx_1859_;
v_isShared_1881_ = v_isSharedCheck_1892_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_synthNormMemo_1878_);
lean_inc(v_instanceTypedMVars_1877_);
lean_inc(v_dAssignment_1876_);
lean_inc(v_eAssignment_1875_);
lean_inc(v_lAssignment_1874_);
lean_inc(v_userNames_1873_);
lean_inc(v_decls_1872_);
lean_inc(v_lDecls_1871_);
lean_inc(v_mvarCounter_1870_);
lean_inc(v_lmvarCounter_1869_);
lean_inc(v_levelAssignDepth_1868_);
lean_inc(v_depth_1867_);
lean_dec(v_mctx_1859_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1892_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1875_, v_mvarId_1854_, v_val_1855_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 8, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_depth_1867_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_levelAssignDepth_1868_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_lmvarCounter_1869_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_mvarCounter_1870_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_lDecls_1871_);
lean_ctor_set(v_reuseFailAlloc_1891_, 5, v_decls_1872_);
lean_ctor_set(v_reuseFailAlloc_1891_, 6, v_userNames_1873_);
lean_ctor_set(v_reuseFailAlloc_1891_, 7, v_lAssignment_1874_);
lean_ctor_set(v_reuseFailAlloc_1891_, 8, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1891_, 9, v_dAssignment_1876_);
lean_ctor_set(v_reuseFailAlloc_1891_, 10, v_instanceTypedMVars_1877_);
lean_ctor_set(v_reuseFailAlloc_1891_, 11, v_synthNormMemo_1878_);
v___x_1885_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1885_);
v___x_1887_ = v___x_1865_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_cache_1860_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_zetaDeltaFVarIds_1861_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_postponed_1862_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_diag_1863_);
v___x_1887_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_st_ref_put(v___y_1856_, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1882_);
return v___x_1889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1894_, lean_object* v_val_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1894_, v_val_1895_, v___y_1896_);
lean_dec(v___y_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; 
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc_ref(v_type_1899_);
v___x_1905_ = lean_infer_type(v_type_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = l_Lean_Meta_whnfD(v_a_1906_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1942_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1942_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1942_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
switch(lean_obj_tag(v_a_1908_))
{
case 3:
{
lean_object* v_u_1912_; lean_object* v___x_1914_; 
lean_dec_ref(v_type_1899_);
v_u_1912_ = lean_ctor_get(v_a_1908_, 0);
lean_inc(v_u_1912_);
lean_dec_ref_known(v_a_1908_, 1);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_u_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_u_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
case 2:
{
lean_object* v_mvarId_1916_; lean_object* v___x_1917_; 
lean_del_object(v___x_1910_);
v_mvarId_1916_ = lean_ctor_get(v_a_1908_, 0);
lean_inc_n(v_mvarId_1916_, 2);
lean_dec_ref_known(v_a_1908_, 1);
v___x_1917_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1916_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; uint8_t v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; 
lean_dec_ref(v_type_1899_);
v___x_1920_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_n(v_a_1921_, 2);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l_Lean_mkSort(v_a_1921_);
v___x_1923_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1916_, v___x_1922_, v_a_1901_);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___x_1923_, 0);
lean_dec(v_unused_1931_);
v___x_1925_ = v___x_1923_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_dec(v___x_1923_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v_a_1921_);
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1921_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_dec(v_mvarId_1916_);
return v___x_1920_;
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_mvarId_1916_);
v___x_1932_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1932_;
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_mvarId_1916_);
lean_dec_ref(v_type_1899_);
v_a_1933_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1917_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1917_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
default: 
{
lean_object* v___x_1941_; 
lean_del_object(v___x_1910_);
lean_dec(v_a_1908_);
v___x_1941_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v_type_1899_);
v_a_1943_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1907_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1907_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_type_1899_);
v_a_1951_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1905_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1905_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Meta_getLevel(v_type_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1966_, lean_object* v_val_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1966_, v_val_1967_, v___y_1969_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1974_, lean_object* v_val_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1974_, v_val_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1983_, v_x_1984_, v_x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, size_t v_x_1989_, size_t v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1988_, v_x_1989_, v_x_1990_, v_x_1991_, v_x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_){
_start:
{
size_t v_x_1504__boxed_2000_; size_t v_x_1505__boxed_2001_; lean_object* v_res_2002_; 
v_x_1504__boxed_2000_ = lean_unbox_usize(v_x_1996_);
lean_dec(v_x_1996_);
v_x_1505__boxed_2001_ = lean_unbox_usize(v_x_1997_);
lean_dec(v_x_1997_);
v_res_2002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_1994_, v_x_1995_, v_x_1504__boxed_2000_, v_x_1505__boxed_2001_, v_x_1998_, v_x_1999_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2003_, lean_object* v_n_2004_, lean_object* v_k_2005_, lean_object* v_v_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2004_, v_k_2005_, v_v_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2008_, size_t v_depth_2009_, lean_object* v_keys_2010_, lean_object* v_vals_2011_, lean_object* v_heq_2012_, lean_object* v_i_2013_, lean_object* v_entries_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2009_, v_keys_2010_, v_vals_2011_, v_i_2013_, v_entries_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2016_, lean_object* v_depth_2017_, lean_object* v_keys_2018_, lean_object* v_vals_2019_, lean_object* v_heq_2020_, lean_object* v_i_2021_, lean_object* v_entries_2022_){
_start:
{
size_t v_depth_boxed_2023_; lean_object* v_res_2024_; 
v_depth_boxed_2023_ = lean_unbox_usize(v_depth_2017_);
lean_dec(v_depth_2017_);
v_res_2024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2016_, v_depth_boxed_2023_, v_keys_2018_, v_vals_2019_, v_heq_2020_, v_i_2021_, v_entries_2022_);
lean_dec_ref(v_vals_2019_);
lean_dec_ref(v_keys_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2026_, v_x_2027_, v_x_2028_, v_x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2031_, lean_object* v_b_2032_, lean_object* v_c_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2036_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
v___x_2039_ = lean_apply_7(v_k_2031_, v_b_2032_, v_c_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, lean_box(0));
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2040_, lean_object* v_b_2041_, lean_object* v_c_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2040_, v_b_2041_, v_c_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2049_, lean_object* v_k_2050_, uint8_t v_cleanupAnnotations_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___f_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2057_, 0, v_k_2050_);
v___x_2058_ = 0;
v___x_2059_ = lean_box(0);
v___x_2060_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2058_, v___x_2059_, v_type_2049_, v___f_2057_, v_cleanupAnnotations_2051_, v___x_2058_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_a_2069_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2060_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2060_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2077_, lean_object* v_k_2078_, lean_object* v_cleanupAnnotations_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2085_; lean_object* v_res_2086_; 
v_cleanupAnnotations_boxed_2085_ = lean_unbox(v_cleanupAnnotations_2079_);
v_res_2086_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2077_, v_k_2078_, v_cleanupAnnotations_boxed_2085_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2087_, lean_object* v_type_2088_, lean_object* v_k_2089_, uint8_t v_cleanupAnnotations_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2088_, v_k_2089_, v_cleanupAnnotations_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2097_, lean_object* v_type_2098_, lean_object* v_k_2099_, lean_object* v_cleanupAnnotations_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2106_; lean_object* v_res_2107_; 
v_cleanupAnnotations_boxed_2106_ = lean_unbox(v_cleanupAnnotations_2100_);
v_res_2107_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2097_, v_type_2098_, v_k_2099_, v_cleanupAnnotations_boxed_2106_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2108_, size_t v_i_2109_, size_t v_stop_2110_, lean_object* v_b_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_eq(v_i_2109_, v_stop_2110_);
if (v___x_2117_ == 0)
{
size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2118_ = ((size_t)1ULL);
v___x_2119_ = lean_usize_sub(v_i_2109_, v___x_2118_);
v___x_2120_ = lean_array_uget_borrowed(v_as_2108_, v___x_2119_);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___x_2120_);
v___x_2121_ = lean_infer_type(v___x_2120_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = l_Lean_Meta_getLevel(v_a_2122_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = l_Lean_mkLevelIMax_x27(v_a_2124_, v_b_2111_);
v_i_2109_ = v___x_2119_;
v_b_2111_ = v___x_2125_;
goto _start;
}
else
{
lean_dec(v_b_2111_);
return v___x_2123_;
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_b_2111_);
v_a_2127_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2121_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2121_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_b_2111_);
return v___x_2135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2136_, lean_object* v_i_2137_, lean_object* v_stop_2138_, lean_object* v_b_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
size_t v_i_boxed_2145_; size_t v_stop_boxed_2146_; lean_object* v_res_2147_; 
v_i_boxed_2145_ = lean_unbox_usize(v_i_2137_);
lean_dec(v_i_2137_);
v_stop_boxed_2146_ = lean_unbox_usize(v_stop_2138_);
lean_dec(v_stop_2138_);
v_res_2147_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2136_, v_i_boxed_2145_, v_stop_boxed_2146_, v_b_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec_ref(v_as_2136_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2148_, lean_object* v_e_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_a_2156_; lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Meta_getLevel(v_e_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = lean_array_get_size(v_xs_2148_);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_nat_dec_lt(v___x_2163_, v___x_2162_);
if (v___x_2164_ == 0)
{
v_a_2156_ = v_a_2161_;
goto v___jp_2155_;
}
else
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_usize_of_nat(v___x_2162_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2148_, v___x_2165_, v___x_2166_, v_a_2161_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v_a_2156_ = v_a_2168_;
goto v___jp_2155_;
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2167_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2167_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
v_a_2177_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2160_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2160_);
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
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = l_Lean_Level_normalize(v_a_2156_);
lean_dec(v_a_2156_);
v___x_2158_ = l_Lean_mkSort(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2185_, lean_object* v_e_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2185_, v_e_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec_ref(v_xs_2185_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___f_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; 
v___f_2200_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2201_ = 0;
v___x_2202_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2194_, v___f_2200_, v___x_2201_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2210_, lean_object* v_k_2211_, uint8_t v_cleanupAnnotations_2212_, uint8_t v_preserveNondepLet_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___f_2219_; uint8_t v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2219_, 0, v_k_2211_);
v___x_2220_ = 1;
v___x_2221_ = 0;
v___x_2222_ = lean_box(0);
v___x_2223_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2210_, v___x_2220_, v___x_2220_, v_preserveNondepLet_2213_, v___x_2221_, v___x_2222_, v___f_2219_, v_cleanupAnnotations_2212_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
v_a_2232_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2223_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2223_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2240_, lean_object* v_k_2241_, lean_object* v_cleanupAnnotations_2242_, lean_object* v_preserveNondepLet_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2249_; uint8_t v_preserveNondepLet_boxed_2250_; lean_object* v_res_2251_; 
v_cleanupAnnotations_boxed_2249_ = lean_unbox(v_cleanupAnnotations_2242_);
v_preserveNondepLet_boxed_2250_ = lean_unbox(v_preserveNondepLet_2243_);
v_res_2251_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2240_, v_k_2241_, v_cleanupAnnotations_boxed_2249_, v_preserveNondepLet_boxed_2250_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2252_, lean_object* v_e_2253_, lean_object* v_k_2254_, uint8_t v_cleanupAnnotations_2255_, uint8_t v_preserveNondepLet_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2253_, v_k_2254_, v_cleanupAnnotations_2255_, v_preserveNondepLet_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2263_, lean_object* v_e_2264_, lean_object* v_k_2265_, lean_object* v_cleanupAnnotations_2266_, lean_object* v_preserveNondepLet_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2273_; uint8_t v_preserveNondepLet_boxed_2274_; lean_object* v_res_2275_; 
v_cleanupAnnotations_boxed_2273_ = lean_unbox(v_cleanupAnnotations_2266_);
v_preserveNondepLet_boxed_2274_ = lean_unbox(v_preserveNondepLet_2267_);
v_res_2275_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2263_, v_e_2264_, v_k_2265_, v_cleanupAnnotations_boxed_2273_, v_preserveNondepLet_boxed_2274_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2276_, lean_object* v_e_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
v___x_2283_ = lean_infer_type(v_e_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; uint8_t v___x_2285_; uint8_t v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = 0;
v___x_2286_ = 1;
v___x_2287_ = 1;
v___x_2288_ = l_Lean_Meta_mkForallFVars(v_xs_2276_, v_a_2284_, v___x_2285_, v___x_2286_, v___x_2285_, v___x_2287_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2288_;
}
else
{
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2289_, lean_object* v_e_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2289_, v_e_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_xs_2289_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___f_2304_; uint8_t v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; 
v___f_2304_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2305_ = 0;
v___x_2306_ = 1;
v___x_2307_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2298_, v___f_2304_, v___x_2305_, v___x_2306_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
return v_res_2314_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2327_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2328_ = l_Lean_MessageData_ofName(v_mvarId_2321_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2331_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2340_, lean_object* v_mvarId_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2348_, lean_object* v_mvarId_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2348_, v_mvarId_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v_mctx_2363_; lean_object* v___x_2364_; 
v___x_2362_ = lean_st_ref_get(v_a_2358_);
v_mctx_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc_ref(v_mctx_2363_);
lean_dec(v___x_2362_);
v___x_2364_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2363_, v_mvarId_2356_);
lean_dec_ref(v_mctx_2363_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
return v___x_2365_;
}
else
{
lean_object* v_val_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_mvarId_2356_);
v_val_2366_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2368_ = v___x_2364_;
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_val_2366_);
lean_dec(v___x_2364_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2374_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v_type_2370_; lean_object* v___x_2372_; 
v_type_2370_ = lean_ctor_get(v_val_2366_, 2);
lean_inc_ref(v_type_2370_);
lean_dec(v_val_2366_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 0);
lean_ctor_set(v___x_2368_, 0, v_type_2370_);
v___x_2372_ = v___x_2368_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_type_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_lctx_2387_; lean_object* v___x_2388_; 
v_lctx_2387_ = lean_ctor_get(v_a_2383_, 2);
lean_inc(v_fvarId_2382_);
lean_inc_ref(v_lctx_2387_);
v___x_2388_ = lean_local_ctx_find(v_lctx_2387_, v_fvarId_2382_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2382_, v_a_2384_, v_a_2385_);
return v___x_2389_;
}
else
{
lean_object* v_val_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_fvarId_2382_);
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
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = l_Lean_LocalDecl_type(v_val_2390_);
lean_dec(v_val_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2405_, v_a_2406_, v_a_2408_, v_a_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
return v_res_2418_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_instMonadEIO___redArg();
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2421_ = l_StateRefT_x27_instMonad___redArg(v___x_2420_);
return v___x_2421_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_instMonadExceptOfEIO___redArg();
return v___x_2424_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___f_2426_; 
v___x_2425_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2426_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2426_, 0, v___x_2425_);
return v___f_2426_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___f_2428_; 
v___x_2427_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2428_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2428_, 0, v___x_2427_);
return v___f_2428_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2429_; lean_object* v___f_2430_; lean_object* v___x_2431_; 
v___f_2429_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2430_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___f_2430_);
lean_ctor_set(v___x_2431_, 1, v___f_2429_);
return v___x_2431_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___f_2433_; 
v___x_2432_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2433_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2433_, 0, v___x_2432_);
return v___f_2433_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___f_2435_; 
v___x_2434_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2435_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2435_, 0, v___x_2434_);
return v___f_2435_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2436_; lean_object* v___f_2437_; lean_object* v___x_2438_; 
v___f_2436_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2437_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___f_2437_);
lean_ctor_set(v___x_2438_, 1, v___f_2436_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2441_, lean_object* v_inferType_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
uint8_t v_cacheInferType_2487_; 
v_cacheInferType_2487_ = lean_ctor_get_uint8(v_a_2443_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2487_ == 0)
{
lean_dec_ref(v_e_2441_);
goto v___jp_2448_;
}
else
{
uint8_t v___x_2488_; 
v___x_2488_ = l_Lean_Expr_hasMVar(v_e_2441_);
if (v___x_2488_ == 0)
{
lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___f_2489_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2491_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2441_, v_a_2443_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2590_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2590_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2590_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2537_; lean_object* v_cache_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2585_; 
v___x_2537_ = lean_st_ref_get(v_a_2444_);
v_cache_2538_ = lean_ctor_get(v___x_2537_, 1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; lean_object* v_unused_2587_; lean_object* v_unused_2588_; lean_object* v_unused_2589_; 
v_unused_2586_ = lean_ctor_get(v___x_2537_, 4);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v___x_2537_, 3);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v___x_2537_, 2);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v___x_2537_, 0);
lean_dec(v_unused_2589_);
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2585_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_cache_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2585_;
goto v_resetjp_2539_;
}
v___jp_2496_:
{
lean_object* v___x_2497_; 
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
v___x_2497_ = lean_apply_5(v_inferType_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, lean_box(0));
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; uint8_t v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
v___x_2499_ = l_Lean_Expr_hasMVar(v_a_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2535_; 
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___x_2497_, 0);
lean_dec(v_unused_2536_);
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2535_;
goto v_resetjp_2500_;
}
else
{
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2535_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v_cache_2504_; lean_object* v_mctx_2505_; lean_object* v_zetaDeltaFVarIds_2506_; lean_object* v_postponed_2507_; lean_object* v_diag_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2534_; 
v___x_2503_ = lean_st_ref_take(v_a_2444_);
v_cache_2504_ = lean_ctor_get(v___x_2503_, 1);
v_mctx_2505_ = lean_ctor_get(v___x_2503_, 0);
v_zetaDeltaFVarIds_2506_ = lean_ctor_get(v___x_2503_, 2);
v_postponed_2507_ = lean_ctor_get(v___x_2503_, 3);
v_diag_2508_ = lean_ctor_get(v___x_2503_, 4);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2510_ = v___x_2503_;
v_isShared_2511_ = v_isSharedCheck_2534_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_diag_2508_);
lean_inc(v_postponed_2507_);
lean_inc(v_zetaDeltaFVarIds_2506_);
lean_inc(v_cache_2504_);
lean_inc(v_mctx_2505_);
lean_dec(v___x_2503_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2534_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_inferType_2512_; lean_object* v_funInfo_2513_; lean_object* v_synthInstance_2514_; lean_object* v_whnf_2515_; lean_object* v_defEqTrans_2516_; lean_object* v_defEqPerm_2517_; lean_object* v_isUnitLike_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2533_; 
v_inferType_2512_ = lean_ctor_get(v_cache_2504_, 0);
v_funInfo_2513_ = lean_ctor_get(v_cache_2504_, 1);
v_synthInstance_2514_ = lean_ctor_get(v_cache_2504_, 2);
v_whnf_2515_ = lean_ctor_get(v_cache_2504_, 3);
v_defEqTrans_2516_ = lean_ctor_get(v_cache_2504_, 4);
v_defEqPerm_2517_ = lean_ctor_get(v_cache_2504_, 5);
v_isUnitLike_2518_ = lean_ctor_get(v_cache_2504_, 6);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_cache_2504_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2520_ = v_cache_2504_;
v_isShared_2521_ = v_isSharedCheck_2533_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_isUnitLike_2518_);
lean_inc(v_defEqPerm_2517_);
lean_inc(v_defEqTrans_2516_);
lean_inc(v_whnf_2515_);
lean_inc(v_synthInstance_2514_);
lean_inc(v_funInfo_2513_);
lean_inc(v_inferType_2512_);
lean_dec(v_cache_2504_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2533_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
lean_inc(v_a_2498_);
v___x_2522_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2489_, v___x_2490_, v_inferType_2512_, v_a_2492_, v_a_2498_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_funInfo_2513_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_synthInstance_2514_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_whnf_2515_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_defEqTrans_2516_);
lean_ctor_set(v_reuseFailAlloc_2532_, 5, v_defEqPerm_2517_);
lean_ctor_set(v_reuseFailAlloc_2532_, 6, v_isUnitLike_2518_);
v___x_2524_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2526_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v___x_2524_);
v___x_2526_ = v___x_2510_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_mctx_2505_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_zetaDeltaFVarIds_2506_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_postponed_2507_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_diag_2508_);
v___x_2526_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = lean_st_ref_put(v_a_2444_, v___x_2526_);
if (v_isShared_2502_ == 0)
{
v___x_2529_ = v___x_2501_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2498_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2498_);
lean_dec(v_a_2492_);
return v___x_2497_;
}
}
else
{
lean_dec(v_a_2492_);
return v___x_2497_;
}
}
v_resetjp_2539_:
{
lean_object* v_inferType_2542_; lean_object* v___x_2543_; 
v_inferType_2542_ = lean_ctor_get(v_cache_2538_, 0);
lean_inc_ref(v_inferType_2542_);
lean_dec_ref(v_cache_2538_);
lean_inc(v_a_2492_);
v___x_2543_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2489_, v___x_2490_, v_inferType_2542_, v_a_2492_);
lean_dec_ref(v_inferType_2542_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v___x_2544_; lean_object* v_toApplicative_2545_; lean_object* v_toFunctor_2546_; lean_object* v_toSeq_2547_; lean_object* v_toSeqLeft_2548_; lean_object* v_toSeqRight_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___f_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; lean_object* v___f_2555_; lean_object* v___f_2556_; lean_object* v___f_2557_; lean_object* v___x_2559_; 
lean_del_object(v___x_2494_);
v___x_2544_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2545_ = lean_ctor_get(v___x_2544_, 0);
v_toFunctor_2546_ = lean_ctor_get(v_toApplicative_2545_, 0);
v_toSeq_2547_ = lean_ctor_get(v_toApplicative_2545_, 2);
v_toSeqLeft_2548_ = lean_ctor_get(v_toApplicative_2545_, 3);
v_toSeqRight_2549_ = lean_ctor_get(v_toApplicative_2545_, 4);
v___f_2550_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2551_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2546_, 2);
v___f_2552_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2552_, 0, v_toFunctor_2546_);
v___f_2553_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2553_, 0, v_toFunctor_2546_);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___f_2552_);
lean_ctor_set(v___x_2554_, 1, v___f_2553_);
lean_inc(v_toSeqRight_2549_);
v___f_2555_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2555_, 0, v_toSeqRight_2549_);
lean_inc(v_toSeqLeft_2548_);
v___f_2556_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2556_, 0, v_toSeqLeft_2548_);
lean_inc(v_toSeq_2547_);
v___f_2557_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2557_, 0, v_toSeq_2547_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 4, v___f_2555_);
lean_ctor_set(v___x_2540_, 3, v___f_2556_);
lean_ctor_set(v___x_2540_, 2, v___f_2557_);
lean_ctor_set(v___x_2540_, 1, v___f_2550_);
lean_ctor_set(v___x_2540_, 0, v___x_2554_);
v___x_2559_ = v___x_2540_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___f_2550_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v___f_2557_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v___f_2556_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v___f_2555_);
v___x_2559_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v_toCold_2566_; lean_object* v_cancelTk_x3f_2567_; 
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v___f_2551_);
v___x_2561_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2562_ = l_Lean_Core_instMonadRefCoreM;
v___x_2563_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2564_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2563_, v___x_2560_);
v___x_2565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2561_);
lean_ctor_set(v___x_2565_, 1, v___x_2562_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
v_toCold_2566_ = lean_ctor_get(v_a_2445_, 0);
v_cancelTk_x3f_2567_ = lean_ctor_get(v_toCold_2566_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2567_) == 1)
{
lean_object* v_val_2568_; uint8_t v___x_2569_; 
v_val_2568_ = lean_ctor_get(v_cancelTk_x3f_2567_, 0);
v___x_2569_ = l_IO_CancelToken_isSet(v_val_2568_);
if (v___x_2569_ == 0)
{
lean_dec_ref_known(v___x_2565_, 3);
goto v___jp_2496_;
}
else
{
lean_object* v___x_2074__overap_2570_; lean_object* v___x_2571_; 
v___x_2074__overap_2570_ = l_Lean_throwInterruptException___redArg(v___x_2565_);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
v___x_2571_ = lean_apply_3(v___x_2074__overap_2570_, v_a_2445_, v_a_2446_, lean_box(0));
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_dec_ref_known(v___x_2571_, 1);
goto v___jp_2496_;
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_a_2492_);
lean_dec_ref(v_inferType_2442_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2565_, 3);
goto v___jp_2496_;
}
}
}
else
{
lean_object* v_val_2581_; lean_object* v___x_2583_; 
lean_del_object(v___x_2540_);
lean_dec(v_a_2492_);
lean_dec_ref(v_inferType_2442_);
v_val_2581_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_val_2581_);
lean_dec_ref_known(v___x_2543_, 1);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v_val_2581_);
v___x_2583_ = v___x_2494_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_val_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_inferType_2442_);
v_a_2591_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2491_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2491_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
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
else
{
lean_dec_ref(v_e_2441_);
goto v___jp_2448_;
}
}
v___jp_2448_:
{
lean_object* v___x_2449_; lean_object* v_toApplicative_2450_; lean_object* v_toFunctor_2451_; lean_object* v_toSeq_2452_; lean_object* v_toSeqLeft_2453_; lean_object* v_toSeqRight_2454_; lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___f_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_toCold_2470_; lean_object* v_cancelTk_x3f_2471_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2450_ = lean_ctor_get(v___x_2449_, 0);
v_toFunctor_2451_ = lean_ctor_get(v_toApplicative_2450_, 0);
v_toSeq_2452_ = lean_ctor_get(v_toApplicative_2450_, 2);
v_toSeqLeft_2453_ = lean_ctor_get(v_toApplicative_2450_, 3);
v_toSeqRight_2454_ = lean_ctor_get(v_toApplicative_2450_, 4);
v___f_2455_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2456_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2451_, 2);
v___f_2457_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2457_, 0, v_toFunctor_2451_);
v___f_2458_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2458_, 0, v_toFunctor_2451_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___f_2457_);
lean_ctor_set(v___x_2459_, 1, v___f_2458_);
lean_inc(v_toSeqRight_2454_);
v___f_2460_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2460_, 0, v_toSeqRight_2454_);
lean_inc(v_toSeqLeft_2453_);
v___f_2461_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2461_, 0, v_toSeqLeft_2453_);
lean_inc(v_toSeq_2452_);
v___f_2462_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2462_, 0, v_toSeq_2452_);
v___x_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2459_);
lean_ctor_set(v___x_2463_, 1, v___f_2455_);
lean_ctor_set(v___x_2463_, 2, v___f_2462_);
lean_ctor_set(v___x_2463_, 3, v___f_2461_);
lean_ctor_set(v___x_2463_, 4, v___f_2460_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___f_2456_);
v___x_2465_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2466_ = l_Lean_Core_instMonadRefCoreM;
v___x_2467_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2468_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2467_, v___x_2464_);
v___x_2469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2465_);
lean_ctor_set(v___x_2469_, 1, v___x_2466_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
v_toCold_2470_ = lean_ctor_get(v_a_2445_, 0);
v_cancelTk_x3f_2471_ = lean_ctor_get(v_toCold_2470_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2471_) == 1)
{
lean_object* v_val_2472_; uint8_t v___x_2473_; 
v_val_2472_ = lean_ctor_get(v_cancelTk_x3f_2471_, 0);
v___x_2473_ = l_IO_CancelToken_isSet(v_val_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref_known(v___x_2469_, 3);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
v___x_2474_ = lean_apply_5(v_inferType_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, lean_box(0));
return v___x_2474_;
}
else
{
lean_object* v___x_2047__overap_2475_; lean_object* v___x_2476_; 
v___x_2047__overap_2475_ = l_Lean_throwInterruptException___redArg(v___x_2469_);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
v___x_2476_ = lean_apply_3(v___x_2047__overap_2475_, v_a_2445_, v_a_2446_, lean_box(0));
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v___x_2477_; 
lean_dec_ref_known(v___x_2476_, 1);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
v___x_2477_ = lean_apply_5(v_inferType_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, lean_box(0));
return v___x_2477_;
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v_inferType_2442_);
v_a_2478_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
else
{
lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2469_, 3);
lean_inc(v_a_2446_);
lean_inc_ref(v_a_2445_);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
v___x_2486_ = lean_apply_5(v_inferType_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, lean_box(0));
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2599_, lean_object* v_inferType_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2599_, v_inferType_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
lean_dec(v_a_2604_);
lean_dec_ref(v_a_2603_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2659_; uint8_t v_beta_2660_; 
v___x_2659_ = l_Lean_Meta_Context_config(v___y_2608_);
v_beta_2660_ = lean_ctor_get_uint8(v___x_2659_, 13);
if (v_beta_2660_ == 0)
{
lean_dec_ref(v___x_2659_);
goto v___jp_2613_;
}
else
{
uint8_t v_iota_2661_; 
v_iota_2661_ = lean_ctor_get_uint8(v___x_2659_, 12);
if (v_iota_2661_ == 0)
{
lean_dec_ref(v___x_2659_);
goto v___jp_2613_;
}
else
{
uint8_t v_zeta_2662_; 
v_zeta_2662_ = lean_ctor_get_uint8(v___x_2659_, 15);
if (v_zeta_2662_ == 0)
{
lean_dec_ref(v___x_2659_);
goto v___jp_2613_;
}
else
{
uint8_t v_zetaHave_2663_; 
v_zetaHave_2663_ = lean_ctor_get_uint8(v___x_2659_, 18);
if (v_zetaHave_2663_ == 0)
{
lean_dec_ref(v___x_2659_);
goto v___jp_2613_;
}
else
{
uint8_t v_zetaDelta_2664_; 
v_zetaDelta_2664_ = lean_ctor_get_uint8(v___x_2659_, 16);
if (v_zetaDelta_2664_ == 0)
{
lean_dec_ref(v___x_2659_);
goto v___jp_2613_;
}
else
{
uint8_t v_etaStruct_2665_; uint8_t v_proj_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_etaStruct_2665_ = lean_ctor_get_uint8(v___x_2659_, 10);
v_proj_2666_ = lean_ctor_get_uint8(v___x_2659_, 14);
lean_dec_ref(v___x_2659_);
v___x_2667_ = lean_box(v_proj_2666_);
v___x_2668_ = lean_obj_tag_nat(v___x_2667_);
lean_dec(v___x_2667_);
v___x_2669_ = lean_unsigned_to_nat(2u);
v___x_2670_ = lean_nat_dec_eq(v___x_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
goto v___jp_2613_;
}
else
{
uint8_t v___x_2671_; uint8_t v___x_2672_; 
v___x_2671_ = 0;
v___x_2672_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2665_, v___x_2671_);
if (v___x_2672_ == 0)
{
goto v___jp_2613_;
}
else
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_apply_5(v_x_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, lean_box(0));
return v___x_2673_;
}
}
}
}
}
}
}
v___jp_2613_:
{
lean_object* v___x_2614_; uint8_t v_foApprox_2615_; uint8_t v_ctxApprox_2616_; uint8_t v_quasiPatternApprox_2617_; uint8_t v_constApprox_2618_; uint8_t v_isDefEqStuckEx_2619_; uint8_t v_unificationHints_2620_; uint8_t v_proofIrrelevance_2621_; uint8_t v_assignSyntheticOpaque_2622_; uint8_t v_offsetCnstrs_2623_; uint8_t v_transparency_2624_; uint8_t v_univApprox_2625_; uint8_t v_zetaUnused_2626_; uint8_t v_canUnfoldPredicateConfig_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2658_; 
v___x_2614_ = l_Lean_Meta_Context_config(v___y_2608_);
v_foApprox_2615_ = lean_ctor_get_uint8(v___x_2614_, 0);
v_ctxApprox_2616_ = lean_ctor_get_uint8(v___x_2614_, 1);
v_quasiPatternApprox_2617_ = lean_ctor_get_uint8(v___x_2614_, 2);
v_constApprox_2618_ = lean_ctor_get_uint8(v___x_2614_, 3);
v_isDefEqStuckEx_2619_ = lean_ctor_get_uint8(v___x_2614_, 4);
v_unificationHints_2620_ = lean_ctor_get_uint8(v___x_2614_, 5);
v_proofIrrelevance_2621_ = lean_ctor_get_uint8(v___x_2614_, 6);
v_assignSyntheticOpaque_2622_ = lean_ctor_get_uint8(v___x_2614_, 7);
v_offsetCnstrs_2623_ = lean_ctor_get_uint8(v___x_2614_, 8);
v_transparency_2624_ = lean_ctor_get_uint8(v___x_2614_, 9);
v_univApprox_2625_ = lean_ctor_get_uint8(v___x_2614_, 11);
v_zetaUnused_2626_ = lean_ctor_get_uint8(v___x_2614_, 17);
v_canUnfoldPredicateConfig_2627_ = lean_ctor_get_uint8(v___x_2614_, 19);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2629_ = v___x_2614_;
v_isShared_2630_ = v_isSharedCheck_2658_;
goto v_resetjp_2628_;
}
else
{
lean_dec(v___x_2614_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2658_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
uint8_t v___x_2631_; uint8_t v___x_2632_; uint8_t v___x_2633_; lean_object* v___x_2635_; 
v___x_2631_ = 1;
v___x_2632_ = 0;
v___x_2633_ = 2;
if (v_isShared_2630_ == 0)
{
v___x_2635_ = v___x_2629_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 0, v_foApprox_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 1, v_ctxApprox_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 2, v_quasiPatternApprox_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 3, v_constApprox_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 4, v_isDefEqStuckEx_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 5, v_unificationHints_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 6, v_proofIrrelevance_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 7, v_assignSyntheticOpaque_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 8, v_offsetCnstrs_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 9, v_transparency_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 11, v_univApprox_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 17, v_zetaUnused_2626_);
lean_ctor_set_uint8(v_reuseFailAlloc_2657_, 19, v_canUnfoldPredicateConfig_2627_);
v___x_2635_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
uint8_t v_trackZetaDelta_2636_; lean_object* v_zetaDeltaSet_2637_; lean_object* v_lctx_2638_; lean_object* v_localInstances_2639_; lean_object* v_defEqCtx_x3f_2640_; lean_object* v_synthPendingDepth_2641_; lean_object* v_customCanUnfoldPredicate_x3f_2642_; uint8_t v_univApprox_2643_; uint8_t v_inTypeClassResolution_2644_; uint8_t v_cacheInferType_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2655_; 
lean_ctor_set_uint8(v___x_2635_, 10, v___x_2632_);
lean_ctor_set_uint8(v___x_2635_, 12, v___x_2631_);
lean_ctor_set_uint8(v___x_2635_, 13, v___x_2631_);
lean_ctor_set_uint8(v___x_2635_, 14, v___x_2633_);
lean_ctor_set_uint8(v___x_2635_, 15, v___x_2631_);
lean_ctor_set_uint8(v___x_2635_, 16, v___x_2631_);
lean_ctor_set_uint8(v___x_2635_, 18, v___x_2631_);
v_trackZetaDelta_2636_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*7);
v_zetaDeltaSet_2637_ = lean_ctor_get(v___y_2608_, 1);
v_lctx_2638_ = lean_ctor_get(v___y_2608_, 2);
v_localInstances_2639_ = lean_ctor_get(v___y_2608_, 3);
v_defEqCtx_x3f_2640_ = lean_ctor_get(v___y_2608_, 4);
v_synthPendingDepth_2641_ = lean_ctor_get(v___y_2608_, 5);
v_customCanUnfoldPredicate_x3f_2642_ = lean_ctor_get(v___y_2608_, 6);
v_univApprox_2643_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2644_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*7 + 2);
v_cacheInferType_2645_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*7 + 3);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___y_2608_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v___y_2608_, 0);
lean_dec(v_unused_2656_);
v___x_2647_ = v___y_2608_;
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2642_);
lean_inc(v_synthPendingDepth_2641_);
lean_inc(v_defEqCtx_x3f_2640_);
lean_inc(v_localInstances_2639_);
lean_inc(v_lctx_2638_);
lean_inc(v_zetaDeltaSet_2637_);
lean_dec(v___y_2608_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2655_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
uint64_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2649_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2635_);
v___x_2650_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2650_, 0, v___x_2635_);
lean_ctor_set_uint64(v___x_2650_, sizeof(void*)*1, v___x_2649_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2650_);
v___x_2652_ = v___x_2647_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_zetaDeltaSet_2637_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_lctx_2638_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_localInstances_2639_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_defEqCtx_x3f_2640_);
lean_ctor_set(v_reuseFailAlloc_2654_, 5, v_synthPendingDepth_2641_);
lean_ctor_set(v_reuseFailAlloc_2654_, 6, v_customCanUnfoldPredicate_x3f_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, sizeof(void*)*7, v_trackZetaDelta_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, sizeof(void*)*7 + 1, v_univApprox_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, sizeof(void*)*7 + 3, v_cacheInferType_2645_);
v___x_2652_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_apply_5(v_x_2607_, v___x_2652_, v___y_2609_, v___y_2610_, v___y_2611_, lean_box(0));
return v___x_2653_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___y_2688_; lean_object* v___x_2705_; uint8_t v_transparency_2706_; uint8_t v___x_2707_; uint8_t v___x_2708_; 
v___x_2705_ = l_Lean_Meta_Context_config(v_a_2682_);
v_transparency_2706_ = lean_ctor_get_uint8(v___x_2705_, 9);
lean_dec_ref(v___x_2705_);
v___x_2707_ = 1;
v___x_2708_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; 
lean_inc(v_a_2685_);
lean_inc_ref(v_a_2684_);
lean_inc(v_a_2683_);
lean_inc_ref(v_a_2682_);
v___x_2709_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
v___y_2688_ = v___x_2709_;
goto v___jp_2687_;
}
else
{
lean_object* v_keyedConfig_2710_; uint8_t v_trackZetaDelta_2711_; lean_object* v_zetaDeltaSet_2712_; lean_object* v_lctx_2713_; lean_object* v_localInstances_2714_; lean_object* v_defEqCtx_x3f_2715_; lean_object* v_synthPendingDepth_2716_; lean_object* v_customCanUnfoldPredicate_x3f_2717_; uint8_t v_univApprox_2718_; uint8_t v_inTypeClassResolution_2719_; uint8_t v_cacheInferType_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_keyedConfig_2710_ = lean_ctor_get(v_a_2682_, 0);
v_trackZetaDelta_2711_ = lean_ctor_get_uint8(v_a_2682_, sizeof(void*)*7);
v_zetaDeltaSet_2712_ = lean_ctor_get(v_a_2682_, 1);
v_lctx_2713_ = lean_ctor_get(v_a_2682_, 2);
v_localInstances_2714_ = lean_ctor_get(v_a_2682_, 3);
v_defEqCtx_x3f_2715_ = lean_ctor_get(v_a_2682_, 4);
v_synthPendingDepth_2716_ = lean_ctor_get(v_a_2682_, 5);
v_customCanUnfoldPredicate_x3f_2717_ = lean_ctor_get(v_a_2682_, 6);
v_univApprox_2718_ = lean_ctor_get_uint8(v_a_2682_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2719_ = lean_ctor_get_uint8(v_a_2682_, sizeof(void*)*7 + 2);
v_cacheInferType_2720_ = lean_ctor_get_uint8(v_a_2682_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2710_);
v___x_2721_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2707_, v_keyedConfig_2710_);
lean_inc(v_customCanUnfoldPredicate_x3f_2717_);
lean_inc(v_synthPendingDepth_2716_);
lean_inc(v_defEqCtx_x3f_2715_);
lean_inc_ref(v_localInstances_2714_);
lean_inc_ref(v_lctx_2713_);
lean_inc(v_zetaDeltaSet_2712_);
v___x_2722_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_zetaDeltaSet_2712_);
lean_ctor_set(v___x_2722_, 2, v_lctx_2713_);
lean_ctor_set(v___x_2722_, 3, v_localInstances_2714_);
lean_ctor_set(v___x_2722_, 4, v_defEqCtx_x3f_2715_);
lean_ctor_set(v___x_2722_, 5, v_synthPendingDepth_2716_);
lean_ctor_set(v___x_2722_, 6, v_customCanUnfoldPredicate_x3f_2717_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7, v_trackZetaDelta_2711_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 1, v_univApprox_2718_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2719_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 3, v_cacheInferType_2720_);
lean_inc(v_a_2685_);
lean_inc_ref(v_a_2684_);
lean_inc(v_a_2683_);
v___x_2723_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2681_, v___x_2722_, v_a_2683_, v_a_2684_, v_a_2685_);
v___y_2688_ = v___x_2723_;
goto v___jp_2687_;
}
v___jp_2687_:
{
if (lean_obj_tag(v___y_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_a_2689_ = lean_ctor_get(v___y_2688_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___y_2688_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___y_2688_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___y_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
v_a_2697_ = lean_ctor_get(v___y_2688_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___y_2688_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___y_2688_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___y_2688_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2731_, lean_object* v_x_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___y_2739_; lean_object* v___x_2756_; uint8_t v_transparency_2757_; uint8_t v___x_2758_; uint8_t v___x_2759_; 
v___x_2756_ = l_Lean_Meta_Context_config(v_a_2733_);
v_transparency_2757_ = lean_ctor_get_uint8(v___x_2756_, 9);
lean_dec_ref(v___x_2756_);
v___x_2758_ = 1;
v___x_2759_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2757_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; 
lean_inc(v_a_2736_);
lean_inc_ref(v_a_2735_);
lean_inc(v_a_2734_);
lean_inc_ref(v_a_2733_);
v___x_2760_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
v___y_2739_ = v___x_2760_;
goto v___jp_2738_;
}
else
{
lean_object* v_keyedConfig_2761_; uint8_t v_trackZetaDelta_2762_; lean_object* v_zetaDeltaSet_2763_; lean_object* v_lctx_2764_; lean_object* v_localInstances_2765_; lean_object* v_defEqCtx_x3f_2766_; lean_object* v_synthPendingDepth_2767_; lean_object* v_customCanUnfoldPredicate_x3f_2768_; uint8_t v_univApprox_2769_; uint8_t v_inTypeClassResolution_2770_; uint8_t v_cacheInferType_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_keyedConfig_2761_ = lean_ctor_get(v_a_2733_, 0);
v_trackZetaDelta_2762_ = lean_ctor_get_uint8(v_a_2733_, sizeof(void*)*7);
v_zetaDeltaSet_2763_ = lean_ctor_get(v_a_2733_, 1);
v_lctx_2764_ = lean_ctor_get(v_a_2733_, 2);
v_localInstances_2765_ = lean_ctor_get(v_a_2733_, 3);
v_defEqCtx_x3f_2766_ = lean_ctor_get(v_a_2733_, 4);
v_synthPendingDepth_2767_ = lean_ctor_get(v_a_2733_, 5);
v_customCanUnfoldPredicate_x3f_2768_ = lean_ctor_get(v_a_2733_, 6);
v_univApprox_2769_ = lean_ctor_get_uint8(v_a_2733_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2770_ = lean_ctor_get_uint8(v_a_2733_, sizeof(void*)*7 + 2);
v_cacheInferType_2771_ = lean_ctor_get_uint8(v_a_2733_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2761_);
v___x_2772_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2758_, v_keyedConfig_2761_);
lean_inc(v_customCanUnfoldPredicate_x3f_2768_);
lean_inc(v_synthPendingDepth_2767_);
lean_inc(v_defEqCtx_x3f_2766_);
lean_inc_ref(v_localInstances_2765_);
lean_inc_ref(v_lctx_2764_);
lean_inc(v_zetaDeltaSet_2763_);
v___x_2773_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v_zetaDeltaSet_2763_);
lean_ctor_set(v___x_2773_, 2, v_lctx_2764_);
lean_ctor_set(v___x_2773_, 3, v_localInstances_2765_);
lean_ctor_set(v___x_2773_, 4, v_defEqCtx_x3f_2766_);
lean_ctor_set(v___x_2773_, 5, v_synthPendingDepth_2767_);
lean_ctor_set(v___x_2773_, 6, v_customCanUnfoldPredicate_x3f_2768_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*7, v_trackZetaDelta_2762_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*7 + 1, v_univApprox_2769_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2770_);
lean_ctor_set_uint8(v___x_2773_, sizeof(void*)*7 + 3, v_cacheInferType_2771_);
lean_inc(v_a_2736_);
lean_inc_ref(v_a_2735_);
lean_inc(v_a_2734_);
v___x_2774_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2732_, v___x_2773_, v_a_2734_, v_a_2735_, v_a_2736_);
v___y_2739_ = v___x_2774_;
goto v___jp_2738_;
}
v___jp_2738_:
{
if (lean_obj_tag(v___y_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
v_a_2740_ = lean_ctor_get(v___y_2739_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___y_2739_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___y_2739_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___y_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_a_2748_ = lean_ctor_get(v___y_2739_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___y_2739_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___y_2739_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___y_2739_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2775_, lean_object* v_x_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2775_, v_x_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
return v_res_2782_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2783_ = lean_box(0);
v___x_2784_ = l_Lean_interruptExceptionId;
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v___x_2783_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2801_, lean_object* v_x_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v_ks_2805_; lean_object* v_vs_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2832_; 
v_ks_2805_ = lean_ctor_get(v_x_2801_, 0);
v_vs_2806_ = lean_ctor_get(v_x_2801_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_x_2801_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2808_ = v_x_2801_;
v_isShared_2809_ = v_isSharedCheck_2832_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_vs_2806_);
lean_inc(v_ks_2805_);
lean_dec(v_x_2801_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2832_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = lean_array_get_size(v_ks_2805_);
v___x_2818_ = lean_nat_dec_lt(v_x_2802_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_del_object(v___x_2808_);
lean_dec(v_x_2802_);
v___x_2819_ = lean_array_push(v_ks_2805_, v_x_2803_);
v___x_2820_ = lean_array_push(v_vs_2806_, v_x_2804_);
v___x_2821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
return v___x_2821_;
}
else
{
lean_object* v_expr_2822_; uint64_t v_configKey_2823_; lean_object* v_k_x27_2824_; lean_object* v_expr_2825_; uint64_t v_configKey_2826_; uint8_t v___x_2827_; 
v_expr_2822_ = lean_ctor_get(v_x_2803_, 0);
v_configKey_2823_ = lean_ctor_get_uint64(v_x_2803_, sizeof(void*)*1);
v_k_x27_2824_ = lean_array_fget_borrowed(v_ks_2805_, v_x_2802_);
v_expr_2825_ = lean_ctor_get(v_k_x27_2824_, 0);
v_configKey_2826_ = lean_ctor_get_uint64(v_k_x27_2824_, sizeof(void*)*1);
v___x_2827_ = lean_expr_equal(v_expr_2822_, v_expr_2825_);
if (v___x_2827_ == 0)
{
goto v___jp_2810_;
}
else
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_uint64_dec_eq(v_configKey_2823_, v_configKey_2826_);
if (v___x_2828_ == 0)
{
goto v___jp_2810_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2808_);
v___x_2829_ = lean_array_fset(v_ks_2805_, v_x_2802_, v_x_2803_);
v___x_2830_ = lean_array_fset(v_vs_2806_, v_x_2802_, v_x_2804_);
lean_dec(v_x_2802_);
v___x_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
return v___x_2831_;
}
}
}
v___jp_2810_:
{
lean_object* v___x_2812_; 
if (v_isShared_2809_ == 0)
{
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_ks_2805_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_vs_2806_);
v___x_2812_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_unsigned_to_nat(1u);
v___x_2814_ = lean_nat_add(v_x_2802_, v___x_2813_);
lean_dec(v_x_2802_);
v_x_2801_ = v___x_2812_;
v_x_2802_ = v___x_2814_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2833_, lean_object* v_k_2834_, lean_object* v_v_2835_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2833_, v___x_2836_, v_k_2834_, v_v_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2838_, size_t v_x_2839_, size_t v_x_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_){
_start:
{
if (lean_obj_tag(v_x_2838_) == 0)
{
lean_object* v_es_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v_j_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v_es_2843_ = lean_ctor_get(v_x_2838_, 0);
v___x_2844_ = ((size_t)31ULL);
v___x_2845_ = lean_usize_land(v_x_2839_, v___x_2844_);
v_j_2846_ = lean_usize_to_nat(v___x_2845_);
v___x_2847_ = lean_array_get_size(v_es_2843_);
v___x_2848_ = lean_nat_dec_lt(v_j_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_dec(v_j_2846_);
lean_dec(v_x_2842_);
lean_dec_ref(v_x_2841_);
return v_x_2838_;
}
else
{
lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2893_; 
lean_inc_ref(v_es_2843_);
v_isSharedCheck_2893_ = !lean_is_exclusive(v_x_2838_);
if (v_isSharedCheck_2893_ == 0)
{
lean_object* v_unused_2894_; 
v_unused_2894_ = lean_ctor_get(v_x_2838_, 0);
lean_dec(v_unused_2894_);
v___x_2850_ = v_x_2838_;
v_isShared_2851_ = v_isSharedCheck_2893_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v_x_2838_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2893_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_v_2852_; lean_object* v___x_2853_; lean_object* v_xs_x27_2854_; lean_object* v___y_2856_; 
v_v_2852_ = lean_array_fget(v_es_2843_, v_j_2846_);
v___x_2853_ = lean_box(0);
v_xs_x27_2854_ = lean_array_fset(v_es_2843_, v_j_2846_, v___x_2853_);
switch(lean_obj_tag(v_v_2852_))
{
case 0:
{
lean_object* v_key_2861_; lean_object* v_val_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2878_; 
v_key_2861_ = lean_ctor_get(v_v_2852_, 0);
v_val_2862_ = lean_ctor_get(v_v_2852_, 1);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_v_2852_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2864_ = v_v_2852_;
v_isShared_2865_ = v_isSharedCheck_2878_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_val_2862_);
lean_inc(v_key_2861_);
lean_dec(v_v_2852_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2878_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v_expr_2869_; uint64_t v_configKey_2870_; lean_object* v_expr_2871_; uint64_t v_configKey_2872_; uint8_t v___x_2873_; 
v_expr_2869_ = lean_ctor_get(v_x_2841_, 0);
v_configKey_2870_ = lean_ctor_get_uint64(v_x_2841_, sizeof(void*)*1);
v_expr_2871_ = lean_ctor_get(v_key_2861_, 0);
v_configKey_2872_ = lean_ctor_get_uint64(v_key_2861_, sizeof(void*)*1);
v___x_2873_ = lean_expr_equal(v_expr_2869_, v_expr_2871_);
if (v___x_2873_ == 0)
{
lean_del_object(v___x_2864_);
goto v___jp_2866_;
}
else
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_uint64_dec_eq(v_configKey_2870_, v_configKey_2872_);
if (v___x_2874_ == 0)
{
lean_del_object(v___x_2864_);
goto v___jp_2866_;
}
else
{
lean_object* v___x_2876_; 
lean_dec(v_val_2862_);
lean_dec(v_key_2861_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 1, v_x_2842_);
lean_ctor_set(v___x_2864_, 0, v_x_2841_);
v___x_2876_ = v___x_2864_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_x_2841_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_x_2842_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
v___y_2856_ = v___x_2876_;
goto v___jp_2855_;
}
}
}
v___jp_2866_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2861_, v_val_2862_, v_x_2841_, v_x_2842_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
v___y_2856_ = v___x_2868_;
goto v___jp_2855_;
}
}
}
case 1:
{
lean_object* v_node_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2891_; 
v_node_2879_ = lean_ctor_get(v_v_2852_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_v_2852_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2881_ = v_v_2852_;
v_isShared_2882_ = v_isSharedCheck_2891_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_node_2879_);
lean_dec(v_v_2852_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2891_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
size_t v___x_2883_; size_t v___x_2884_; size_t v___x_2885_; size_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2883_ = ((size_t)5ULL);
v___x_2884_ = lean_usize_shift_right(v_x_2839_, v___x_2883_);
v___x_2885_ = ((size_t)1ULL);
v___x_2886_ = lean_usize_add(v_x_2840_, v___x_2885_);
v___x_2887_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2879_, v___x_2884_, v___x_2886_, v_x_2841_, v_x_2842_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2887_);
v___x_2889_ = v___x_2881_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
v___y_2856_ = v___x_2889_;
goto v___jp_2855_;
}
}
}
default: 
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v_x_2841_);
lean_ctor_set(v___x_2892_, 1, v_x_2842_);
v___y_2856_ = v___x_2892_;
goto v___jp_2855_;
}
}
v___jp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_array_fset(v_xs_x27_2854_, v_j_2846_, v___y_2856_);
lean_dec(v_j_2846_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2857_);
v___x_2859_ = v___x_2850_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
else
{
lean_object* v_ks_2895_; lean_object* v_vs_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2914_; 
v_ks_2895_ = lean_ctor_get(v_x_2838_, 0);
v_vs_2896_ = lean_ctor_get(v_x_2838_, 1);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_x_2838_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2898_ = v_x_2838_;
v_isShared_2899_ = v_isSharedCheck_2914_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_vs_2896_);
lean_inc(v_ks_2895_);
lean_dec(v_x_2838_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2914_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_ks_2895_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_vs_2896_);
v___x_2901_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v_newNode_2902_; size_t v___x_2903_; uint8_t v___x_2904_; 
v_newNode_2902_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2901_, v_x_2841_, v_x_2842_);
v___x_2903_ = ((size_t)7ULL);
v___x_2904_ = lean_usize_dec_le(v___x_2903_, v_x_2840_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2905_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2902_);
v___x_2906_ = lean_unsigned_to_nat(4u);
v___x_2907_ = lean_nat_dec_lt(v___x_2905_, v___x_2906_);
lean_dec(v___x_2905_);
if (v___x_2907_ == 0)
{
lean_object* v_ks_2908_; lean_object* v_vs_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_ks_2908_ = lean_ctor_get(v_newNode_2902_, 0);
lean_inc_ref(v_ks_2908_);
v_vs_2909_ = lean_ctor_get(v_newNode_2902_, 1);
lean_inc_ref(v_vs_2909_);
lean_dec_ref(v_newNode_2902_);
v___x_2910_ = lean_unsigned_to_nat(0u);
v___x_2911_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2840_, v_ks_2908_, v_vs_2909_, v___x_2910_, v___x_2911_);
lean_dec_ref(v_vs_2909_);
lean_dec_ref(v_ks_2908_);
return v___x_2912_;
}
else
{
return v_newNode_2902_;
}
}
else
{
return v_newNode_2902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2915_, lean_object* v_keys_2916_, lean_object* v_vals_2917_, lean_object* v_i_2918_, lean_object* v_entries_2919_){
_start:
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = lean_array_get_size(v_keys_2916_);
v___x_2921_ = lean_nat_dec_lt(v_i_2918_, v___x_2920_);
if (v___x_2921_ == 0)
{
lean_dec(v_i_2918_);
return v_entries_2919_;
}
else
{
lean_object* v_k_2922_; lean_object* v_expr_2923_; uint64_t v_configKey_2924_; lean_object* v_v_2925_; uint64_t v___x_2926_; uint64_t v___x_2927_; size_t v_h_2928_; size_t v___x_2929_; lean_object* v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; size_t v_h_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_k_2922_ = lean_array_fget_borrowed(v_keys_2916_, v_i_2918_);
v_expr_2923_ = lean_ctor_get(v_k_2922_, 0);
v_configKey_2924_ = lean_ctor_get_uint64(v_k_2922_, sizeof(void*)*1);
v_v_2925_ = lean_array_fget_borrowed(v_vals_2917_, v_i_2918_);
v___x_2926_ = l_Lean_Expr_hash(v_expr_2923_);
v___x_2927_ = lean_uint64_mix_hash(v___x_2926_, v_configKey_2924_);
v_h_2928_ = lean_uint64_to_usize(v___x_2927_);
v___x_2929_ = ((size_t)5ULL);
v___x_2930_ = lean_unsigned_to_nat(1u);
v___x_2931_ = ((size_t)1ULL);
v___x_2932_ = lean_usize_sub(v_depth_2915_, v___x_2931_);
v___x_2933_ = lean_usize_mul(v___x_2929_, v___x_2932_);
v_h_2934_ = lean_usize_shift_right(v_h_2928_, v___x_2933_);
v___x_2935_ = lean_nat_add(v_i_2918_, v___x_2930_);
lean_dec(v_i_2918_);
lean_inc(v_v_2925_);
lean_inc(v_k_2922_);
v___x_2936_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2919_, v_h_2934_, v_depth_2915_, v_k_2922_, v_v_2925_);
v_i_2918_ = v___x_2935_;
v_entries_2919_ = v___x_2936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2938_, lean_object* v_keys_2939_, lean_object* v_vals_2940_, lean_object* v_i_2941_, lean_object* v_entries_2942_){
_start:
{
size_t v_depth_boxed_2943_; lean_object* v_res_2944_; 
v_depth_boxed_2943_ = lean_unbox_usize(v_depth_2938_);
lean_dec(v_depth_2938_);
v_res_2944_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2943_, v_keys_2939_, v_vals_2940_, v_i_2941_, v_entries_2942_);
lean_dec_ref(v_vals_2940_);
lean_dec_ref(v_keys_2939_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
size_t v_x_2430__boxed_2950_; size_t v_x_2431__boxed_2951_; lean_object* v_res_2952_; 
v_x_2430__boxed_2950_ = lean_unbox_usize(v_x_2946_);
lean_dec(v_x_2946_);
v_x_2431__boxed_2951_ = lean_unbox_usize(v_x_2947_);
lean_dec(v_x_2947_);
v_res_2952_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2945_, v_x_2430__boxed_2950_, v_x_2431__boxed_2951_, v_x_2948_, v_x_2949_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2953_, lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
lean_object* v_expr_2956_; uint64_t v_configKey_2957_; uint64_t v___x_2958_; uint64_t v___x_2959_; size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; 
v_expr_2956_ = lean_ctor_get(v_x_2954_, 0);
v_configKey_2957_ = lean_ctor_get_uint64(v_x_2954_, sizeof(void*)*1);
v___x_2958_ = l_Lean_Expr_hash(v_expr_2956_);
v___x_2959_ = lean_uint64_mix_hash(v___x_2958_, v_configKey_2957_);
v___x_2960_ = lean_uint64_to_usize(v___x_2959_);
v___x_2961_ = ((size_t)1ULL);
v___x_2962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2953_, v___x_2960_, v___x_2961_, v_x_2954_, v_x_2955_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2963_, lean_object* v_vals_2964_, lean_object* v_i_2965_, lean_object* v_k_2966_){
_start:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_array_get_size(v_keys_2963_);
v___x_2972_ = lean_nat_dec_lt(v_i_2965_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; 
lean_dec(v_i_2965_);
v___x_2973_ = lean_box(0);
return v___x_2973_;
}
else
{
lean_object* v_expr_2974_; uint64_t v_configKey_2975_; lean_object* v_k_x27_2976_; lean_object* v_expr_2977_; uint64_t v_configKey_2978_; uint8_t v___x_2979_; 
v_expr_2974_ = lean_ctor_get(v_k_2966_, 0);
v_configKey_2975_ = lean_ctor_get_uint64(v_k_2966_, sizeof(void*)*1);
v_k_x27_2976_ = lean_array_fget_borrowed(v_keys_2963_, v_i_2965_);
v_expr_2977_ = lean_ctor_get(v_k_x27_2976_, 0);
v_configKey_2978_ = lean_ctor_get_uint64(v_k_x27_2976_, sizeof(void*)*1);
v___x_2979_ = lean_expr_equal(v_expr_2974_, v_expr_2977_);
if (v___x_2979_ == 0)
{
goto v___jp_2967_;
}
else
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_uint64_dec_eq(v_configKey_2975_, v_configKey_2978_);
if (v___x_2980_ == 0)
{
goto v___jp_2967_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = lean_array_fget_borrowed(v_vals_2964_, v_i_2965_);
lean_dec(v_i_2965_);
lean_inc(v___x_2981_);
v___x_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
return v___x_2982_;
}
}
}
v___jp_2967_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_unsigned_to_nat(1u);
v___x_2969_ = lean_nat_add(v_i_2965_, v___x_2968_);
lean_dec(v_i_2965_);
v_i_2965_ = v___x_2969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_2983_, lean_object* v_vals_2984_, lean_object* v_i_2985_, lean_object* v_k_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_2983_, v_vals_2984_, v_i_2985_, v_k_2986_);
lean_dec_ref(v_k_2986_);
lean_dec_ref(v_vals_2984_);
lean_dec_ref(v_keys_2983_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_2988_, size_t v_x_2989_, lean_object* v_x_2990_){
_start:
{
if (lean_obj_tag(v_x_2988_) == 0)
{
lean_object* v_es_2991_; lean_object* v___x_2992_; size_t v___x_2993_; size_t v___x_2994_; lean_object* v_j_2995_; lean_object* v___x_2996_; 
v_es_2991_ = lean_ctor_get(v_x_2988_, 0);
v___x_2992_ = lean_box(2);
v___x_2993_ = ((size_t)31ULL);
v___x_2994_ = lean_usize_land(v_x_2989_, v___x_2993_);
v_j_2995_ = lean_usize_to_nat(v___x_2994_);
v___x_2996_ = lean_array_get_borrowed(v___x_2992_, v_es_2991_, v_j_2995_);
lean_dec(v_j_2995_);
switch(lean_obj_tag(v___x_2996_))
{
case 0:
{
lean_object* v_key_2997_; lean_object* v_val_2998_; lean_object* v_expr_2999_; uint64_t v_configKey_3000_; lean_object* v_expr_3001_; uint64_t v_configKey_3002_; uint8_t v___x_3003_; 
v_key_2997_ = lean_ctor_get(v___x_2996_, 0);
v_val_2998_ = lean_ctor_get(v___x_2996_, 1);
v_expr_2999_ = lean_ctor_get(v_x_2990_, 0);
v_configKey_3000_ = lean_ctor_get_uint64(v_x_2990_, sizeof(void*)*1);
v_expr_3001_ = lean_ctor_get(v_key_2997_, 0);
v_configKey_3002_ = lean_ctor_get_uint64(v_key_2997_, sizeof(void*)*1);
v___x_3003_ = lean_expr_equal(v_expr_2999_, v_expr_3001_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_box(0);
return v___x_3004_;
}
else
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_uint64_dec_eq(v_configKey_3000_, v_configKey_3002_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_box(0);
return v___x_3006_;
}
else
{
lean_object* v___x_3007_; 
lean_inc(v_val_2998_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_val_2998_);
return v___x_3007_;
}
}
}
case 1:
{
lean_object* v_node_3008_; size_t v___x_3009_; size_t v___x_3010_; 
v_node_3008_ = lean_ctor_get(v___x_2996_, 0);
v___x_3009_ = ((size_t)5ULL);
v___x_3010_ = lean_usize_shift_right(v_x_2989_, v___x_3009_);
v_x_2988_ = v_node_3008_;
v_x_2989_ = v___x_3010_;
goto _start;
}
default: 
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_box(0);
return v___x_3012_;
}
}
}
else
{
lean_object* v_ks_3013_; lean_object* v_vs_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_ks_3013_ = lean_ctor_get(v_x_2988_, 0);
v_vs_3014_ = lean_ctor_get(v_x_2988_, 1);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3013_, v_vs_3014_, v___x_3015_, v_x_2990_);
return v___x_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
size_t v_x_2630__boxed_3020_; lean_object* v_res_3021_; 
v_x_2630__boxed_3020_ = lean_unbox_usize(v_x_3018_);
lean_dec(v_x_3018_);
v_res_3021_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3017_, v_x_2630__boxed_3020_, v_x_3019_);
lean_dec_ref(v_x_3019_);
lean_dec_ref(v_x_3017_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v_expr_3024_; uint64_t v_configKey_3025_; uint64_t v___x_3026_; uint64_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v_expr_3024_ = lean_ctor_get(v_x_3023_, 0);
v_configKey_3025_ = lean_ctor_get_uint64(v_x_3023_, sizeof(void*)*1);
v___x_3026_ = l_Lean_Expr_hash(v_expr_3024_);
v___x_3027_ = lean_uint64_mix_hash(v___x_3026_, v_configKey_3025_);
v___x_3028_ = lean_uint64_to_usize(v___x_3027_);
v___x_3029_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3022_, v___x_3028_, v_x_3023_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3030_, lean_object* v_x_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3030_, v_x_3031_);
lean_dec_ref(v_x_3031_);
lean_dec_ref(v_x_3030_);
return v_res_3032_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
switch(lean_obj_tag(v_e_3036_))
{
case 0:
{
lean_object* v_deBruijnIndex_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_deBruijnIndex_3074_ = lean_ctor_get(v_e_3036_, 0);
lean_inc(v_deBruijnIndex_3074_);
lean_dec_ref_known(v_e_3036_, 1);
v___x_3075_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3076_ = l_Lean_mkBVar(v_deBruijnIndex_3074_);
v___x_3077_ = l_Lean_MessageData_ofExpr(v___x_3076_);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3075_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3078_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3079_;
}
case 1:
{
lean_object* v_fvarId_3080_; lean_object* v___x_3081_; 
v_fvarId_3080_ = lean_ctor_get(v_e_3036_, 0);
lean_inc(v_fvarId_3080_);
lean_dec_ref_known(v_e_3036_, 1);
v___x_3081_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3080_, v_a_3037_, v_a_3039_, v_a_3040_);
return v___x_3081_;
}
case 2:
{
lean_object* v_mvarId_3082_; lean_object* v___x_3083_; 
v_mvarId_3082_ = lean_ctor_get(v_e_3036_, 0);
lean_inc(v_mvarId_3082_);
lean_dec_ref_known(v_e_3036_, 1);
v___x_3083_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3082_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3083_;
}
case 3:
{
lean_object* v_u_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_u_3084_ = lean_ctor_get(v_e_3036_, 0);
lean_inc(v_u_3084_);
lean_dec_ref_known(v_e_3036_, 1);
v___x_3085_ = l_Lean_Level_succ___override(v_u_3084_);
v___x_3086_ = l_Lean_mkSort(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
case 4:
{
lean_object* v_declName_3088_; lean_object* v_us_3089_; 
v_declName_3088_ = lean_ctor_get(v_e_3036_, 0);
lean_inc(v_declName_3088_);
v_us_3089_ = lean_ctor_get(v_e_3036_, 1);
lean_inc(v_us_3089_);
if (lean_obj_tag(v_us_3089_) == 0)
{
lean_object* v___x_3106_; 
lean_dec_ref_known(v_e_3036_, 2);
v___x_3106_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3088_, v_us_3089_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3106_;
}
else
{
uint8_t v_cacheInferType_3107_; 
v_cacheInferType_3107_ = lean_ctor_get_uint8(v_a_3037_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3107_ == 0)
{
lean_dec_ref_known(v_e_3036_, 2);
goto v___jp_3090_;
}
else
{
uint8_t v___x_3108_; 
v___x_3108_ = l_Lean_Expr_hasMVar(v_e_3036_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3176_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3176_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3176_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3155_; lean_object* v_cache_3156_; lean_object* v_inferType_3157_; lean_object* v___x_3158_; 
v___x_3155_ = lean_st_ref_get(v_a_3038_);
v_cache_3156_ = lean_ctor_get(v___x_3155_, 1);
lean_inc_ref(v_cache_3156_);
lean_dec(v___x_3155_);
v_inferType_3157_ = lean_ctor_get(v_cache_3156_, 0);
lean_inc_ref(v_inferType_3157_);
lean_dec_ref(v_cache_3156_);
v___x_3158_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3157_, v_a_3110_);
lean_dec_ref(v_inferType_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_toCold_3159_; lean_object* v_cancelTk_x3f_3160_; 
lean_del_object(v___x_3112_);
v_toCold_3159_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3160_ = lean_ctor_get(v_toCold_3159_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3160_) == 1)
{
lean_object* v_val_3161_; uint8_t v___x_3162_; 
v_val_3161_ = lean_ctor_get(v_cancelTk_x3f_3160_, 0);
v___x_3162_ = l_IO_CancelToken_isSet(v_val_3161_);
if (v___x_3162_ == 0)
{
goto v___jp_3114_;
}
else
{
lean_object* v___x_3163_; lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_a_3110_);
lean_dec(v_us_3089_);
lean_dec(v_declName_3088_);
v___x_3163_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
goto v___jp_3114_;
}
}
else
{
lean_object* v_val_3172_; lean_object* v___x_3174_; 
lean_dec(v_a_3110_);
lean_dec(v_us_3089_);
lean_dec(v_declName_3088_);
v_val_3172_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_val_3172_);
lean_dec_ref_known(v___x_3158_, 1);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v_val_3172_);
v___x_3174_ = v___x_3112_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_val_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
v___jp_3114_:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3088_, v_us_3089_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; uint8_t v___x_3117_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v___x_3117_ = l_Lean_Expr_hasMVar(v_a_3116_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3153_; 
lean_inc(v_a_3116_);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v___x_3115_, 0);
lean_dec(v_unused_3154_);
v___x_3119_ = v___x_3115_;
v_isShared_3120_ = v_isSharedCheck_3153_;
goto v_resetjp_3118_;
}
else
{
lean_dec(v___x_3115_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3153_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v_cache_3122_; lean_object* v_mctx_3123_; lean_object* v_zetaDeltaFVarIds_3124_; lean_object* v_postponed_3125_; lean_object* v_diag_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3152_; 
v___x_3121_ = lean_st_ref_take(v_a_3038_);
v_cache_3122_ = lean_ctor_get(v___x_3121_, 1);
v_mctx_3123_ = lean_ctor_get(v___x_3121_, 0);
v_zetaDeltaFVarIds_3124_ = lean_ctor_get(v___x_3121_, 2);
v_postponed_3125_ = lean_ctor_get(v___x_3121_, 3);
v_diag_3126_ = lean_ctor_get(v___x_3121_, 4);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3128_ = v___x_3121_;
v_isShared_3129_ = v_isSharedCheck_3152_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_diag_3126_);
lean_inc(v_postponed_3125_);
lean_inc(v_zetaDeltaFVarIds_3124_);
lean_inc(v_cache_3122_);
lean_inc(v_mctx_3123_);
lean_dec(v___x_3121_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3152_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v_inferType_3130_; lean_object* v_funInfo_3131_; lean_object* v_synthInstance_3132_; lean_object* v_whnf_3133_; lean_object* v_defEqTrans_3134_; lean_object* v_defEqPerm_3135_; lean_object* v_isUnitLike_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3151_; 
v_inferType_3130_ = lean_ctor_get(v_cache_3122_, 0);
v_funInfo_3131_ = lean_ctor_get(v_cache_3122_, 1);
v_synthInstance_3132_ = lean_ctor_get(v_cache_3122_, 2);
v_whnf_3133_ = lean_ctor_get(v_cache_3122_, 3);
v_defEqTrans_3134_ = lean_ctor_get(v_cache_3122_, 4);
v_defEqPerm_3135_ = lean_ctor_get(v_cache_3122_, 5);
v_isUnitLike_3136_ = lean_ctor_get(v_cache_3122_, 6);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_cache_3122_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3138_ = v_cache_3122_;
v_isShared_3139_ = v_isSharedCheck_3151_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_isUnitLike_3136_);
lean_inc(v_defEqPerm_3135_);
lean_inc(v_defEqTrans_3134_);
lean_inc(v_whnf_3133_);
lean_inc(v_synthInstance_3132_);
lean_inc(v_funInfo_3131_);
lean_inc(v_inferType_3130_);
lean_dec(v_cache_3122_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3151_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
lean_inc(v_a_3116_);
v___x_3140_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3130_, v_a_3110_, v_a_3116_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_funInfo_3131_);
lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_synthInstance_3132_);
lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_whnf_3133_);
lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_defEqTrans_3134_);
lean_ctor_set(v_reuseFailAlloc_3150_, 5, v_defEqPerm_3135_);
lean_ctor_set(v_reuseFailAlloc_3150_, 6, v_isUnitLike_3136_);
v___x_3142_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3144_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 1, v___x_3142_);
v___x_3144_ = v___x_3128_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_mctx_3123_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_zetaDeltaFVarIds_3124_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_postponed_3125_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v_diag_3126_);
v___x_3144_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_st_ref_put(v_a_3038_, v___x_3144_);
if (v_isShared_3120_ == 0)
{
v___x_3147_ = v___x_3119_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3116_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3110_);
return v___x_3115_;
}
}
else
{
lean_dec(v_a_3110_);
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_us_3089_);
lean_dec(v_declName_3088_);
v_a_3177_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3109_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3109_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3036_, 2);
goto v___jp_3090_;
}
}
}
v___jp_3090_:
{
lean_object* v_toCold_3091_; lean_object* v_cancelTk_x3f_3092_; 
v_toCold_3091_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3092_ = lean_ctor_get(v_toCold_3091_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3092_) == 1)
{
lean_object* v_val_3093_; uint8_t v___x_3094_; 
v_val_3093_ = lean_ctor_get(v_cancelTk_x3f_3092_, 0);
v___x_3094_ = l_IO_CancelToken_isSet(v_val_3093_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3088_, v_us_3089_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3095_;
}
else
{
lean_object* v___x_3096_; lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_us_3089_);
lean_dec(v_declName_3088_);
v___x_3096_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3088_, v_us_3089_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3105_;
}
}
}
case 5:
{
lean_object* v_fn_3185_; uint8_t v_cacheInferType_3186_; lean_object* v_nargs_3187_; lean_object* v___x_3188_; lean_object* v_dummy_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_fn_3185_ = lean_ctor_get(v_e_3036_, 0);
v_cacheInferType_3186_ = lean_ctor_get_uint8(v_a_3037_, sizeof(void*)*7 + 3);
v_nargs_3187_ = l_Lean_Expr_getAppNumArgs(v_e_3036_);
v___x_3188_ = l_Lean_Expr_getAppFn(v_fn_3185_);
v_dummy_3189_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3187_);
v___x_3190_ = lean_mk_array(v_nargs_3187_, v_dummy_3189_);
v___x_3191_ = lean_unsigned_to_nat(1u);
v___x_3192_ = lean_nat_sub(v_nargs_3187_, v___x_3191_);
lean_dec(v_nargs_3187_);
lean_inc_ref(v_e_3036_);
v___x_3193_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3036_, v___x_3190_, v___x_3192_);
if (v_cacheInferType_3186_ == 0)
{
lean_dec_ref_known(v_e_3036_, 2);
goto v___jp_3194_;
}
else
{
uint8_t v___x_3210_; 
v___x_3210_ = l_Lean_Expr_hasMVar(v_e_3036_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3278_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3278_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3278_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3257_; lean_object* v_cache_3258_; lean_object* v_inferType_3259_; lean_object* v___x_3260_; 
v___x_3257_ = lean_st_ref_get(v_a_3038_);
v_cache_3258_ = lean_ctor_get(v___x_3257_, 1);
lean_inc_ref(v_cache_3258_);
lean_dec(v___x_3257_);
v_inferType_3259_ = lean_ctor_get(v_cache_3258_, 0);
lean_inc_ref(v_inferType_3259_);
lean_dec_ref(v_cache_3258_);
v___x_3260_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3259_, v_a_3212_);
lean_dec_ref(v_inferType_3259_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_toCold_3261_; lean_object* v_cancelTk_x3f_3262_; 
lean_del_object(v___x_3214_);
v_toCold_3261_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3262_ = lean_ctor_get(v_toCold_3261_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3262_) == 1)
{
lean_object* v_val_3263_; uint8_t v___x_3264_; 
v_val_3263_ = lean_ctor_get(v_cancelTk_x3f_3262_, 0);
v___x_3264_ = l_IO_CancelToken_isSet(v_val_3263_);
if (v___x_3264_ == 0)
{
goto v___jp_3216_;
}
else
{
lean_object* v___x_3265_; lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec(v_a_3212_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v___x_3188_);
v___x_3265_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
else
{
goto v___jp_3216_;
}
}
else
{
lean_object* v_val_3274_; lean_object* v___x_3276_; 
lean_dec(v_a_3212_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v___x_3188_);
v_val_3274_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v___x_3260_, 1);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v_val_3274_);
v___x_3276_ = v___x_3214_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_val_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
v___jp_3216_:
{
lean_object* v___x_3217_; 
v___x_3217_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3188_, v___x_3193_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec_ref(v___x_3193_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; uint8_t v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v___x_3219_ = l_Lean_Expr_hasMVar(v_a_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3255_; 
lean_inc(v_a_3218_);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3255_ == 0)
{
lean_object* v_unused_3256_; 
v_unused_3256_ = lean_ctor_get(v___x_3217_, 0);
lean_dec(v_unused_3256_);
v___x_3221_ = v___x_3217_;
v_isShared_3222_ = v_isSharedCheck_3255_;
goto v_resetjp_3220_;
}
else
{
lean_dec(v___x_3217_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3255_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v_cache_3224_; lean_object* v_mctx_3225_; lean_object* v_zetaDeltaFVarIds_3226_; lean_object* v_postponed_3227_; lean_object* v_diag_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3254_; 
v___x_3223_ = lean_st_ref_take(v_a_3038_);
v_cache_3224_ = lean_ctor_get(v___x_3223_, 1);
v_mctx_3225_ = lean_ctor_get(v___x_3223_, 0);
v_zetaDeltaFVarIds_3226_ = lean_ctor_get(v___x_3223_, 2);
v_postponed_3227_ = lean_ctor_get(v___x_3223_, 3);
v_diag_3228_ = lean_ctor_get(v___x_3223_, 4);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3230_ = v___x_3223_;
v_isShared_3231_ = v_isSharedCheck_3254_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_diag_3228_);
lean_inc(v_postponed_3227_);
lean_inc(v_zetaDeltaFVarIds_3226_);
lean_inc(v_cache_3224_);
lean_inc(v_mctx_3225_);
lean_dec(v___x_3223_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3254_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v_inferType_3232_; lean_object* v_funInfo_3233_; lean_object* v_synthInstance_3234_; lean_object* v_whnf_3235_; lean_object* v_defEqTrans_3236_; lean_object* v_defEqPerm_3237_; lean_object* v_isUnitLike_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3253_; 
v_inferType_3232_ = lean_ctor_get(v_cache_3224_, 0);
v_funInfo_3233_ = lean_ctor_get(v_cache_3224_, 1);
v_synthInstance_3234_ = lean_ctor_get(v_cache_3224_, 2);
v_whnf_3235_ = lean_ctor_get(v_cache_3224_, 3);
v_defEqTrans_3236_ = lean_ctor_get(v_cache_3224_, 4);
v_defEqPerm_3237_ = lean_ctor_get(v_cache_3224_, 5);
v_isUnitLike_3238_ = lean_ctor_get(v_cache_3224_, 6);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_cache_3224_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3240_ = v_cache_3224_;
v_isShared_3241_ = v_isSharedCheck_3253_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_isUnitLike_3238_);
lean_inc(v_defEqPerm_3237_);
lean_inc(v_defEqTrans_3236_);
lean_inc(v_whnf_3235_);
lean_inc(v_synthInstance_3234_);
lean_inc(v_funInfo_3233_);
lean_inc(v_inferType_3232_);
lean_dec(v_cache_3224_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3253_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_inc(v_a_3218_);
v___x_3242_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3232_, v_a_3212_, v_a_3218_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3242_);
v___x_3244_ = v___x_3240_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_funInfo_3233_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_synthInstance_3234_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_whnf_3235_);
lean_ctor_set(v_reuseFailAlloc_3252_, 4, v_defEqTrans_3236_);
lean_ctor_set(v_reuseFailAlloc_3252_, 5, v_defEqPerm_3237_);
lean_ctor_set(v_reuseFailAlloc_3252_, 6, v_isUnitLike_3238_);
v___x_3244_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3246_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 1, v___x_3244_);
v___x_3246_ = v___x_3230_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_mctx_3225_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3251_, 2, v_zetaDeltaFVarIds_3226_);
lean_ctor_set(v_reuseFailAlloc_3251_, 3, v_postponed_3227_);
lean_ctor_set(v_reuseFailAlloc_3251_, 4, v_diag_3228_);
v___x_3246_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3247_ = lean_st_ref_put(v_a_3038_, v___x_3246_);
if (v_isShared_3222_ == 0)
{
v___x_3249_ = v___x_3221_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3218_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3212_);
return v___x_3217_;
}
}
else
{
lean_dec(v_a_3212_);
return v___x_3217_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v___x_3193_);
lean_dec_ref(v___x_3188_);
v_a_3279_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3211_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3211_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3036_, 2);
goto v___jp_3194_;
}
}
v___jp_3194_:
{
lean_object* v_toCold_3195_; lean_object* v_cancelTk_x3f_3196_; 
v_toCold_3195_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3196_ = lean_ctor_get(v_toCold_3195_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3196_) == 1)
{
lean_object* v_val_3197_; uint8_t v___x_3198_; 
v_val_3197_ = lean_ctor_get(v_cancelTk_x3f_3196_, 0);
v___x_3198_ = l_IO_CancelToken_isSet(v_val_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
v___x_3199_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3188_, v___x_3193_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec_ref(v___x_3193_);
return v___x_3199_;
}
else
{
lean_object* v___x_3200_; lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v___x_3193_);
lean_dec_ref(v___x_3188_);
v___x_3200_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v___x_3209_; 
v___x_3209_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3188_, v___x_3193_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
lean_dec_ref(v___x_3193_);
return v___x_3209_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3287_; 
v_cacheInferType_3287_ = lean_ctor_get_uint8(v_a_3037_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3287_ == 0)
{
goto v___jp_3058_;
}
else
{
uint8_t v___x_3288_; 
v___x_3288_ = l_Lean_Expr_hasMVar(v_e_3036_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
lean_inc_ref(v_e_3036_);
v___x_3289_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3356_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3356_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3356_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3335_; lean_object* v_cache_3336_; lean_object* v_inferType_3337_; lean_object* v___x_3338_; 
v___x_3335_ = lean_st_ref_get(v_a_3038_);
v_cache_3336_ = lean_ctor_get(v___x_3335_, 1);
lean_inc_ref(v_cache_3336_);
lean_dec(v___x_3335_);
v_inferType_3337_ = lean_ctor_get(v_cache_3336_, 0);
lean_inc_ref(v_inferType_3337_);
lean_dec_ref(v_cache_3336_);
v___x_3338_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3337_, v_a_3290_);
lean_dec_ref(v_inferType_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_toCold_3339_; lean_object* v_cancelTk_x3f_3340_; 
lean_del_object(v___x_3292_);
v_toCold_3339_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3340_ = lean_ctor_get(v_toCold_3339_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3340_) == 1)
{
lean_object* v_val_3341_; uint8_t v___x_3342_; 
v_val_3341_ = lean_ctor_get(v_cancelTk_x3f_3340_, 0);
v___x_3342_ = l_IO_CancelToken_isSet(v_val_3341_);
if (v___x_3342_ == 0)
{
goto v___jp_3294_;
}
else
{
lean_object* v___x_3343_; lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v_a_3290_);
lean_dec_ref_known(v_e_3036_, 3);
v___x_3343_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
else
{
goto v___jp_3294_;
}
}
else
{
lean_object* v_val_3352_; lean_object* v___x_3354_; 
lean_dec(v_a_3290_);
lean_dec_ref_known(v_e_3036_, 3);
v_val_3352_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3352_);
lean_dec_ref_known(v___x_3338_, 1);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_val_3352_);
v___x_3354_ = v___x_3292_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_val_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
v___jp_3294_:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; uint8_t v___x_3297_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v___x_3297_ = l_Lean_Expr_hasMVar(v_a_3296_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3333_; 
lean_inc(v_a_3296_);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v___x_3295_, 0);
lean_dec(v_unused_3334_);
v___x_3299_ = v___x_3295_;
v_isShared_3300_ = v_isSharedCheck_3333_;
goto v_resetjp_3298_;
}
else
{
lean_dec(v___x_3295_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3333_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; lean_object* v_cache_3302_; lean_object* v_mctx_3303_; lean_object* v_zetaDeltaFVarIds_3304_; lean_object* v_postponed_3305_; lean_object* v_diag_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3332_; 
v___x_3301_ = lean_st_ref_take(v_a_3038_);
v_cache_3302_ = lean_ctor_get(v___x_3301_, 1);
v_mctx_3303_ = lean_ctor_get(v___x_3301_, 0);
v_zetaDeltaFVarIds_3304_ = lean_ctor_get(v___x_3301_, 2);
v_postponed_3305_ = lean_ctor_get(v___x_3301_, 3);
v_diag_3306_ = lean_ctor_get(v___x_3301_, 4);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3308_ = v___x_3301_;
v_isShared_3309_ = v_isSharedCheck_3332_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_diag_3306_);
lean_inc(v_postponed_3305_);
lean_inc(v_zetaDeltaFVarIds_3304_);
lean_inc(v_cache_3302_);
lean_inc(v_mctx_3303_);
lean_dec(v___x_3301_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3332_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_inferType_3310_; lean_object* v_funInfo_3311_; lean_object* v_synthInstance_3312_; lean_object* v_whnf_3313_; lean_object* v_defEqTrans_3314_; lean_object* v_defEqPerm_3315_; lean_object* v_isUnitLike_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3331_; 
v_inferType_3310_ = lean_ctor_get(v_cache_3302_, 0);
v_funInfo_3311_ = lean_ctor_get(v_cache_3302_, 1);
v_synthInstance_3312_ = lean_ctor_get(v_cache_3302_, 2);
v_whnf_3313_ = lean_ctor_get(v_cache_3302_, 3);
v_defEqTrans_3314_ = lean_ctor_get(v_cache_3302_, 4);
v_defEqPerm_3315_ = lean_ctor_get(v_cache_3302_, 5);
v_isUnitLike_3316_ = lean_ctor_get(v_cache_3302_, 6);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_cache_3302_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3318_ = v_cache_3302_;
v_isShared_3319_ = v_isSharedCheck_3331_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_isUnitLike_3316_);
lean_inc(v_defEqPerm_3315_);
lean_inc(v_defEqTrans_3314_);
lean_inc(v_whnf_3313_);
lean_inc(v_synthInstance_3312_);
lean_inc(v_funInfo_3311_);
lean_inc(v_inferType_3310_);
lean_dec(v_cache_3302_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3331_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
lean_inc(v_a_3296_);
v___x_3320_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3310_, v_a_3290_, v_a_3296_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3320_);
v___x_3322_ = v___x_3318_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3320_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_funInfo_3311_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_synthInstance_3312_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v_whnf_3313_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v_defEqTrans_3314_);
lean_ctor_set(v_reuseFailAlloc_3330_, 5, v_defEqPerm_3315_);
lean_ctor_set(v_reuseFailAlloc_3330_, 6, v_isUnitLike_3316_);
v___x_3322_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
lean_object* v___x_3324_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v___x_3322_);
v___x_3324_ = v___x_3308_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_mctx_3303_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_zetaDeltaFVarIds_3304_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_postponed_3305_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_diag_3306_);
v___x_3324_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = lean_st_ref_put(v_a_3038_, v___x_3324_);
if (v_isShared_3300_ == 0)
{
v___x_3327_ = v___x_3299_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3296_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3290_);
return v___x_3295_;
}
}
else
{
lean_dec(v_a_3290_);
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec_ref_known(v_e_3036_, 3);
v_a_3357_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3289_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3289_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
goto v___jp_3058_;
}
}
}
case 9:
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_a_3365_ = lean_ctor_get(v_e_3036_, 0);
lean_inc_ref(v_a_3365_);
lean_dec_ref_known(v_e_3036_, 1);
v___x_3366_ = l_Lean_Literal_type(v_a_3365_);
lean_dec_ref(v_a_3365_);
v___x_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
return v___x_3367_;
}
case 10:
{
lean_object* v_expr_3368_; 
v_expr_3368_ = lean_ctor_get(v_e_3036_, 1);
lean_inc_ref(v_expr_3368_);
lean_dec_ref_known(v_e_3036_, 2);
v_e_3036_ = v_expr_3368_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3370_; lean_object* v_idx_3371_; lean_object* v_struct_3372_; uint8_t v_cacheInferType_3389_; 
v_typeName_3370_ = lean_ctor_get(v_e_3036_, 0);
lean_inc(v_typeName_3370_);
v_idx_3371_ = lean_ctor_get(v_e_3036_, 1);
lean_inc(v_idx_3371_);
v_struct_3372_ = lean_ctor_get(v_e_3036_, 2);
lean_inc_ref(v_struct_3372_);
v_cacheInferType_3389_ = lean_ctor_get_uint8(v_a_3037_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3389_ == 0)
{
lean_dec_ref_known(v_e_3036_, 3);
goto v___jp_3373_;
}
else
{
uint8_t v___x_3390_; 
v___x_3390_ = l_Lean_Expr_hasMVar(v_e_3036_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3458_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3458_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3458_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3437_; lean_object* v_cache_3438_; lean_object* v_inferType_3439_; lean_object* v___x_3440_; 
v___x_3437_ = lean_st_ref_get(v_a_3038_);
v_cache_3438_ = lean_ctor_get(v___x_3437_, 1);
lean_inc_ref(v_cache_3438_);
lean_dec(v___x_3437_);
v_inferType_3439_ = lean_ctor_get(v_cache_3438_, 0);
lean_inc_ref(v_inferType_3439_);
lean_dec_ref(v_cache_3438_);
v___x_3440_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3439_, v_a_3392_);
lean_dec_ref(v_inferType_3439_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_toCold_3441_; lean_object* v_cancelTk_x3f_3442_; 
lean_del_object(v___x_3394_);
v_toCold_3441_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3442_ = lean_ctor_get(v_toCold_3441_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3442_) == 1)
{
lean_object* v_val_3443_; uint8_t v___x_3444_; 
v_val_3443_ = lean_ctor_get(v_cancelTk_x3f_3442_, 0);
v___x_3444_ = l_IO_CancelToken_isSet(v_val_3443_);
if (v___x_3444_ == 0)
{
goto v___jp_3396_;
}
else
{
lean_object* v___x_3445_; lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v_a_3392_);
lean_dec_ref(v_struct_3372_);
lean_dec(v_idx_3371_);
lean_dec(v_typeName_3370_);
v___x_3445_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
goto v___jp_3396_;
}
}
else
{
lean_object* v_val_3454_; lean_object* v___x_3456_; 
lean_dec(v_a_3392_);
lean_dec_ref(v_struct_3372_);
lean_dec(v_idx_3371_);
lean_dec(v_typeName_3370_);
v_val_3454_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v___x_3440_, 1);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 0, v_val_3454_);
v___x_3456_ = v___x_3394_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_val_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
v___jp_3396_:
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3370_, v_idx_3371_, v_struct_3372_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; uint8_t v___x_3399_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v___x_3399_ = l_Lean_Expr_hasMVar(v_a_3398_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3435_; 
lean_inc(v_a_3398_);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3397_, 0);
lean_dec(v_unused_3436_);
v___x_3401_ = v___x_3397_;
v_isShared_3402_ = v_isSharedCheck_3435_;
goto v_resetjp_3400_;
}
else
{
lean_dec(v___x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3435_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v_cache_3404_; lean_object* v_mctx_3405_; lean_object* v_zetaDeltaFVarIds_3406_; lean_object* v_postponed_3407_; lean_object* v_diag_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3434_; 
v___x_3403_ = lean_st_ref_take(v_a_3038_);
v_cache_3404_ = lean_ctor_get(v___x_3403_, 1);
v_mctx_3405_ = lean_ctor_get(v___x_3403_, 0);
v_zetaDeltaFVarIds_3406_ = lean_ctor_get(v___x_3403_, 2);
v_postponed_3407_ = lean_ctor_get(v___x_3403_, 3);
v_diag_3408_ = lean_ctor_get(v___x_3403_, 4);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3410_ = v___x_3403_;
v_isShared_3411_ = v_isSharedCheck_3434_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_diag_3408_);
lean_inc(v_postponed_3407_);
lean_inc(v_zetaDeltaFVarIds_3406_);
lean_inc(v_cache_3404_);
lean_inc(v_mctx_3405_);
lean_dec(v___x_3403_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3434_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_inferType_3412_; lean_object* v_funInfo_3413_; lean_object* v_synthInstance_3414_; lean_object* v_whnf_3415_; lean_object* v_defEqTrans_3416_; lean_object* v_defEqPerm_3417_; lean_object* v_isUnitLike_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3433_; 
v_inferType_3412_ = lean_ctor_get(v_cache_3404_, 0);
v_funInfo_3413_ = lean_ctor_get(v_cache_3404_, 1);
v_synthInstance_3414_ = lean_ctor_get(v_cache_3404_, 2);
v_whnf_3415_ = lean_ctor_get(v_cache_3404_, 3);
v_defEqTrans_3416_ = lean_ctor_get(v_cache_3404_, 4);
v_defEqPerm_3417_ = lean_ctor_get(v_cache_3404_, 5);
v_isUnitLike_3418_ = lean_ctor_get(v_cache_3404_, 6);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_cache_3404_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3420_ = v_cache_3404_;
v_isShared_3421_ = v_isSharedCheck_3433_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_isUnitLike_3418_);
lean_inc(v_defEqPerm_3417_);
lean_inc(v_defEqTrans_3416_);
lean_inc(v_whnf_3415_);
lean_inc(v_synthInstance_3414_);
lean_inc(v_funInfo_3413_);
lean_inc(v_inferType_3412_);
lean_dec(v_cache_3404_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3433_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_inc(v_a_3398_);
v___x_3422_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3412_, v_a_3392_, v_a_3398_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_funInfo_3413_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_synthInstance_3414_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_whnf_3415_);
lean_ctor_set(v_reuseFailAlloc_3432_, 4, v_defEqTrans_3416_);
lean_ctor_set(v_reuseFailAlloc_3432_, 5, v_defEqPerm_3417_);
lean_ctor_set(v_reuseFailAlloc_3432_, 6, v_isUnitLike_3418_);
v___x_3424_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v___x_3424_);
v___x_3426_ = v___x_3410_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_mctx_3405_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_zetaDeltaFVarIds_3406_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_postponed_3407_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_diag_3408_);
v___x_3426_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_st_ref_put(v_a_3038_, v___x_3426_);
if (v_isShared_3402_ == 0)
{
v___x_3429_ = v___x_3401_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3398_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3392_);
return v___x_3397_;
}
}
else
{
lean_dec(v_a_3392_);
return v___x_3397_;
}
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v_struct_3372_);
lean_dec(v_idx_3371_);
lean_dec(v_typeName_3370_);
v_a_3459_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3391_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3391_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3036_, 3);
goto v___jp_3373_;
}
}
v___jp_3373_:
{
lean_object* v_toCold_3374_; lean_object* v_cancelTk_x3f_3375_; 
v_toCold_3374_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3375_ = lean_ctor_get(v_toCold_3374_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3375_) == 1)
{
lean_object* v_val_3376_; uint8_t v___x_3377_; 
v_val_3376_ = lean_ctor_get(v_cancelTk_x3f_3375_, 0);
v___x_3377_ = l_IO_CancelToken_isSet(v_val_3376_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3370_, v_idx_3371_, v_struct_3372_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3378_;
}
else
{
lean_object* v___x_3379_; lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v_struct_3372_);
lean_dec(v_idx_3371_);
lean_dec(v_typeName_3370_);
v___x_3379_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
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
else
{
lean_object* v___x_3388_; 
v___x_3388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3370_, v_idx_3371_, v_struct_3372_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3388_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3467_; 
v_cacheInferType_3467_ = lean_ctor_get_uint8(v_a_3037_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3467_ == 0)
{
goto v___jp_3042_;
}
else
{
uint8_t v___x_3468_; 
v___x_3468_ = l_Lean_Expr_hasMVar(v_e_3036_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_inc_ref(v_e_3036_);
v___x_3469_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3536_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3472_ = v___x_3469_;
v_isShared_3473_ = v_isSharedCheck_3536_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3536_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3515_; lean_object* v_cache_3516_; lean_object* v_inferType_3517_; lean_object* v___x_3518_; 
v___x_3515_ = lean_st_ref_get(v_a_3038_);
v_cache_3516_ = lean_ctor_get(v___x_3515_, 1);
lean_inc_ref(v_cache_3516_);
lean_dec(v___x_3515_);
v_inferType_3517_ = lean_ctor_get(v_cache_3516_, 0);
lean_inc_ref(v_inferType_3517_);
lean_dec_ref(v_cache_3516_);
v___x_3518_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3517_, v_a_3470_);
lean_dec_ref(v_inferType_3517_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_toCold_3519_; lean_object* v_cancelTk_x3f_3520_; 
lean_del_object(v___x_3472_);
v_toCold_3519_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3520_ = lean_ctor_get(v_toCold_3519_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3520_) == 1)
{
lean_object* v_val_3521_; uint8_t v___x_3522_; 
v_val_3521_ = lean_ctor_get(v_cancelTk_x3f_3520_, 0);
v___x_3522_ = l_IO_CancelToken_isSet(v_val_3521_);
if (v___x_3522_ == 0)
{
goto v___jp_3474_;
}
else
{
lean_object* v___x_3523_; lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec(v_a_3470_);
lean_dec_ref(v_e_3036_);
v___x_3523_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
else
{
goto v___jp_3474_;
}
}
else
{
lean_object* v_val_3532_; lean_object* v___x_3534_; 
lean_dec(v_a_3470_);
lean_dec_ref(v_e_3036_);
v_val_3532_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_val_3532_);
lean_dec_ref_known(v___x_3518_, 1);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v_val_3532_);
v___x_3534_ = v___x_3472_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_val_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
v___jp_3474_:
{
lean_object* v___x_3475_; 
v___x_3475_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; uint8_t v___x_3477_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v___x_3477_ = l_Lean_Expr_hasMVar(v_a_3476_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3513_; 
lean_inc(v_a_3476_);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3513_ == 0)
{
lean_object* v_unused_3514_; 
v_unused_3514_ = lean_ctor_get(v___x_3475_, 0);
lean_dec(v_unused_3514_);
v___x_3479_ = v___x_3475_;
v_isShared_3480_ = v_isSharedCheck_3513_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v___x_3475_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3513_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v_cache_3482_; lean_object* v_mctx_3483_; lean_object* v_zetaDeltaFVarIds_3484_; lean_object* v_postponed_3485_; lean_object* v_diag_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3512_; 
v___x_3481_ = lean_st_ref_take(v_a_3038_);
v_cache_3482_ = lean_ctor_get(v___x_3481_, 1);
v_mctx_3483_ = lean_ctor_get(v___x_3481_, 0);
v_zetaDeltaFVarIds_3484_ = lean_ctor_get(v___x_3481_, 2);
v_postponed_3485_ = lean_ctor_get(v___x_3481_, 3);
v_diag_3486_ = lean_ctor_get(v___x_3481_, 4);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3488_ = v___x_3481_;
v_isShared_3489_ = v_isSharedCheck_3512_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_diag_3486_);
lean_inc(v_postponed_3485_);
lean_inc(v_zetaDeltaFVarIds_3484_);
lean_inc(v_cache_3482_);
lean_inc(v_mctx_3483_);
lean_dec(v___x_3481_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3512_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v_inferType_3490_; lean_object* v_funInfo_3491_; lean_object* v_synthInstance_3492_; lean_object* v_whnf_3493_; lean_object* v_defEqTrans_3494_; lean_object* v_defEqPerm_3495_; lean_object* v_isUnitLike_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3511_; 
v_inferType_3490_ = lean_ctor_get(v_cache_3482_, 0);
v_funInfo_3491_ = lean_ctor_get(v_cache_3482_, 1);
v_synthInstance_3492_ = lean_ctor_get(v_cache_3482_, 2);
v_whnf_3493_ = lean_ctor_get(v_cache_3482_, 3);
v_defEqTrans_3494_ = lean_ctor_get(v_cache_3482_, 4);
v_defEqPerm_3495_ = lean_ctor_get(v_cache_3482_, 5);
v_isUnitLike_3496_ = lean_ctor_get(v_cache_3482_, 6);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_cache_3482_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3498_ = v_cache_3482_;
v_isShared_3499_ = v_isSharedCheck_3511_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_isUnitLike_3496_);
lean_inc(v_defEqPerm_3495_);
lean_inc(v_defEqTrans_3494_);
lean_inc(v_whnf_3493_);
lean_inc(v_synthInstance_3492_);
lean_inc(v_funInfo_3491_);
lean_inc(v_inferType_3490_);
lean_dec(v_cache_3482_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3511_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
lean_inc(v_a_3476_);
v___x_3500_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3490_, v_a_3470_, v_a_3476_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3500_);
v___x_3502_ = v___x_3498_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_funInfo_3491_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_synthInstance_3492_);
lean_ctor_set(v_reuseFailAlloc_3510_, 3, v_whnf_3493_);
lean_ctor_set(v_reuseFailAlloc_3510_, 4, v_defEqTrans_3494_);
lean_ctor_set(v_reuseFailAlloc_3510_, 5, v_defEqPerm_3495_);
lean_ctor_set(v_reuseFailAlloc_3510_, 6, v_isUnitLike_3496_);
v___x_3502_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 1, v___x_3502_);
v___x_3504_ = v___x_3488_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_mctx_3483_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3509_, 2, v_zetaDeltaFVarIds_3484_);
lean_ctor_set(v_reuseFailAlloc_3509_, 3, v_postponed_3485_);
lean_ctor_set(v_reuseFailAlloc_3509_, 4, v_diag_3486_);
v___x_3504_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
v___x_3505_ = lean_st_ref_put(v_a_3038_, v___x_3504_);
if (v_isShared_3480_ == 0)
{
v___x_3507_ = v___x_3479_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3476_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3470_);
return v___x_3475_;
}
}
else
{
lean_dec(v_a_3470_);
return v___x_3475_;
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_e_3036_);
v_a_3537_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3469_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3469_);
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
goto v___jp_3042_;
}
}
}
}
v___jp_3042_:
{
lean_object* v_toCold_3043_; lean_object* v_cancelTk_x3f_3044_; 
v_toCold_3043_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3044_ = lean_ctor_get(v_toCold_3043_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3044_) == 1)
{
lean_object* v_val_3045_; uint8_t v___x_3046_; 
v_val_3045_ = lean_ctor_get(v_cancelTk_x3f_3044_, 0);
v___x_3046_ = l_IO_CancelToken_isSet(v_val_3045_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
v___x_3047_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3047_;
}
else
{
lean_object* v___x_3048_; lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v_e_3036_);
v___x_3048_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3057_;
}
}
v___jp_3058_:
{
lean_object* v_toCold_3059_; lean_object* v_cancelTk_x3f_3060_; 
v_toCold_3059_ = lean_ctor_get(v_a_3039_, 0);
v_cancelTk_x3f_3060_ = lean_ctor_get(v_toCold_3059_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3060_) == 1)
{
lean_object* v_val_3061_; uint8_t v___x_3062_; 
v_val_3061_ = lean_ctor_get(v_cancelTk_x3f_3060_, 0);
v___x_3062_ = l_IO_CancelToken_isSet(v_val_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref(v_e_3036_);
v___x_3064_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_);
return v___x_3073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3552_, lean_object* v_x_3553_, lean_object* v_x_3554_, lean_object* v_x_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3553_, v_x_3554_, v_x_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3558_, v_x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3561_, lean_object* v_x_3562_, lean_object* v_x_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3561_, v_x_3562_, v_x_3563_);
lean_dec_ref(v_x_3563_);
lean_dec_ref(v_x_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3565_, lean_object* v_x_3566_, size_t v_x_3567_, size_t v_x_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3566_, v_x_3567_, v_x_3568_, v_x_3569_, v_x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_, lean_object* v_x_3577_){
_start:
{
size_t v_x_3676__boxed_3578_; size_t v_x_3677__boxed_3579_; lean_object* v_res_3580_; 
v_x_3676__boxed_3578_ = lean_unbox_usize(v_x_3574_);
lean_dec(v_x_3574_);
v_x_3677__boxed_3579_ = lean_unbox_usize(v_x_3575_);
lean_dec(v_x_3575_);
v_res_3580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3572_, v_x_3573_, v_x_3676__boxed_3578_, v_x_3677__boxed_3579_, v_x_3576_, v_x_3577_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3581_, lean_object* v_x_3582_, size_t v_x_3583_, lean_object* v_x_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3582_, v_x_3583_, v_x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
size_t v_x_3693__boxed_3590_; lean_object* v_res_3591_; 
v_x_3693__boxed_3590_ = lean_unbox_usize(v_x_3588_);
lean_dec(v_x_3588_);
v_res_3591_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3586_, v_x_3587_, v_x_3693__boxed_3590_, v_x_3589_);
lean_dec_ref(v_x_3589_);
lean_dec_ref(v_x_3587_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3592_, lean_object* v_n_3593_, lean_object* v_k_3594_, lean_object* v_v_3595_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3593_, v_k_3594_, v_v_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3597_, size_t v_depth_3598_, lean_object* v_keys_3599_, lean_object* v_vals_3600_, lean_object* v_heq_3601_, lean_object* v_i_3602_, lean_object* v_entries_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3598_, v_keys_3599_, v_vals_3600_, v_i_3602_, v_entries_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3605_, lean_object* v_depth_3606_, lean_object* v_keys_3607_, lean_object* v_vals_3608_, lean_object* v_heq_3609_, lean_object* v_i_3610_, lean_object* v_entries_3611_){
_start:
{
size_t v_depth_boxed_3612_; lean_object* v_res_3613_; 
v_depth_boxed_3612_ = lean_unbox_usize(v_depth_3606_);
lean_dec(v_depth_3606_);
v_res_3613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3605_, v_depth_boxed_3612_, v_keys_3607_, v_vals_3608_, v_heq_3609_, v_i_3610_, v_entries_3611_);
lean_dec_ref(v_vals_3608_);
lean_dec_ref(v_keys_3607_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3614_, lean_object* v_keys_3615_, lean_object* v_vals_3616_, lean_object* v_heq_3617_, lean_object* v_i_3618_, lean_object* v_k_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3615_, v_vals_3616_, v_i_3618_, v_k_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3621_, lean_object* v_keys_3622_, lean_object* v_vals_3623_, lean_object* v_heq_3624_, lean_object* v_i_3625_, lean_object* v_k_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3621_, v_keys_3622_, v_vals_3623_, v_heq_3624_, v_i_3625_, v_k_3626_);
lean_dec_ref(v_k_3626_);
lean_dec_ref(v_vals_3623_);
lean_dec_ref(v_keys_3622_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3629_, v_x_3630_, v_x_3631_, v_x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = l_Lean_maxRecDepthErrorMessage;
v___x_3640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
return v___x_3640_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3642_ = l_Lean_MessageData_ofFormat(v___x_3641_);
return v___x_3642_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3644_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3645_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
lean_ctor_set(v___x_3645_, 1, v___x_3643_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3646_){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v_ref_3646_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3651_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3654_, lean_object* v_ref_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3655_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3662_, lean_object* v_ref_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3662_, v_ref_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v___x_3722_; uint8_t v_beta_3723_; 
v___x_3722_ = l_Lean_Meta_Context_config(v___y_3671_);
v_beta_3723_ = lean_ctor_get_uint8(v___x_3722_, 13);
if (v_beta_3723_ == 0)
{
lean_dec_ref(v___x_3722_);
goto v___jp_3676_;
}
else
{
uint8_t v_iota_3724_; 
v_iota_3724_ = lean_ctor_get_uint8(v___x_3722_, 12);
if (v_iota_3724_ == 0)
{
lean_dec_ref(v___x_3722_);
goto v___jp_3676_;
}
else
{
uint8_t v_zeta_3725_; 
v_zeta_3725_ = lean_ctor_get_uint8(v___x_3722_, 15);
if (v_zeta_3725_ == 0)
{
lean_dec_ref(v___x_3722_);
goto v___jp_3676_;
}
else
{
uint8_t v_zetaHave_3726_; 
v_zetaHave_3726_ = lean_ctor_get_uint8(v___x_3722_, 18);
if (v_zetaHave_3726_ == 0)
{
lean_dec_ref(v___x_3722_);
goto v___jp_3676_;
}
else
{
uint8_t v_zetaDelta_3727_; 
v_zetaDelta_3727_ = lean_ctor_get_uint8(v___x_3722_, 16);
if (v_zetaDelta_3727_ == 0)
{
lean_dec_ref(v___x_3722_);
goto v___jp_3676_;
}
else
{
uint8_t v_etaStruct_3728_; uint8_t v_proj_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v_etaStruct_3728_ = lean_ctor_get_uint8(v___x_3722_, 10);
v_proj_3729_ = lean_ctor_get_uint8(v___x_3722_, 14);
lean_dec_ref(v___x_3722_);
v___x_3730_ = lean_box(v_proj_3729_);
v___x_3731_ = lean_obj_tag_nat(v___x_3730_);
lean_dec(v___x_3730_);
v___x_3732_ = lean_unsigned_to_nat(2u);
v___x_3733_ = lean_nat_dec_eq(v___x_3731_, v___x_3732_);
if (v___x_3733_ == 0)
{
goto v___jp_3676_;
}
else
{
uint8_t v___x_3734_; uint8_t v___x_3735_; 
v___x_3734_ = 0;
v___x_3735_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3728_, v___x_3734_);
if (v___x_3735_ == 0)
{
goto v___jp_3676_;
}
else
{
lean_object* v___x_3736_; 
v___x_3736_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec_ref(v___y_3671_);
return v___x_3736_;
}
}
}
}
}
}
}
v___jp_3676_:
{
lean_object* v___x_3677_; uint8_t v_foApprox_3678_; uint8_t v_ctxApprox_3679_; uint8_t v_quasiPatternApprox_3680_; uint8_t v_constApprox_3681_; uint8_t v_isDefEqStuckEx_3682_; uint8_t v_unificationHints_3683_; uint8_t v_proofIrrelevance_3684_; uint8_t v_assignSyntheticOpaque_3685_; uint8_t v_offsetCnstrs_3686_; uint8_t v_transparency_3687_; uint8_t v_univApprox_3688_; uint8_t v_zetaUnused_3689_; uint8_t v_canUnfoldPredicateConfig_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3721_; 
v___x_3677_ = l_Lean_Meta_Context_config(v___y_3671_);
v_foApprox_3678_ = lean_ctor_get_uint8(v___x_3677_, 0);
v_ctxApprox_3679_ = lean_ctor_get_uint8(v___x_3677_, 1);
v_quasiPatternApprox_3680_ = lean_ctor_get_uint8(v___x_3677_, 2);
v_constApprox_3681_ = lean_ctor_get_uint8(v___x_3677_, 3);
v_isDefEqStuckEx_3682_ = lean_ctor_get_uint8(v___x_3677_, 4);
v_unificationHints_3683_ = lean_ctor_get_uint8(v___x_3677_, 5);
v_proofIrrelevance_3684_ = lean_ctor_get_uint8(v___x_3677_, 6);
v_assignSyntheticOpaque_3685_ = lean_ctor_get_uint8(v___x_3677_, 7);
v_offsetCnstrs_3686_ = lean_ctor_get_uint8(v___x_3677_, 8);
v_transparency_3687_ = lean_ctor_get_uint8(v___x_3677_, 9);
v_univApprox_3688_ = lean_ctor_get_uint8(v___x_3677_, 11);
v_zetaUnused_3689_ = lean_ctor_get_uint8(v___x_3677_, 17);
v_canUnfoldPredicateConfig_3690_ = lean_ctor_get_uint8(v___x_3677_, 19);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3692_ = v___x_3677_;
v_isShared_3693_ = v_isSharedCheck_3721_;
goto v_resetjp_3691_;
}
else
{
lean_dec(v___x_3677_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3721_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
uint8_t v___x_3694_; uint8_t v___x_3695_; uint8_t v___x_3696_; lean_object* v___x_3698_; 
v___x_3694_ = 1;
v___x_3695_ = 0;
v___x_3696_ = 2;
if (v_isShared_3693_ == 0)
{
v___x_3698_ = v___x_3692_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 0, v_foApprox_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 1, v_ctxApprox_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 2, v_quasiPatternApprox_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 3, v_constApprox_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 4, v_isDefEqStuckEx_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 5, v_unificationHints_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 6, v_proofIrrelevance_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 7, v_assignSyntheticOpaque_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 8, v_offsetCnstrs_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 9, v_transparency_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 11, v_univApprox_3688_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 17, v_zetaUnused_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3720_, 19, v_canUnfoldPredicateConfig_3690_);
v___x_3698_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
uint8_t v_trackZetaDelta_3699_; lean_object* v_zetaDeltaSet_3700_; lean_object* v_lctx_3701_; lean_object* v_localInstances_3702_; lean_object* v_defEqCtx_x3f_3703_; lean_object* v_synthPendingDepth_3704_; lean_object* v_customCanUnfoldPredicate_x3f_3705_; uint8_t v_univApprox_3706_; uint8_t v_inTypeClassResolution_3707_; uint8_t v_cacheInferType_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3718_; 
lean_ctor_set_uint8(v___x_3698_, 10, v___x_3695_);
lean_ctor_set_uint8(v___x_3698_, 12, v___x_3694_);
lean_ctor_set_uint8(v___x_3698_, 13, v___x_3694_);
lean_ctor_set_uint8(v___x_3698_, 14, v___x_3696_);
lean_ctor_set_uint8(v___x_3698_, 15, v___x_3694_);
lean_ctor_set_uint8(v___x_3698_, 16, v___x_3694_);
lean_ctor_set_uint8(v___x_3698_, 18, v___x_3694_);
v_trackZetaDelta_3699_ = lean_ctor_get_uint8(v___y_3671_, sizeof(void*)*7);
v_zetaDeltaSet_3700_ = lean_ctor_get(v___y_3671_, 1);
v_lctx_3701_ = lean_ctor_get(v___y_3671_, 2);
v_localInstances_3702_ = lean_ctor_get(v___y_3671_, 3);
v_defEqCtx_x3f_3703_ = lean_ctor_get(v___y_3671_, 4);
v_synthPendingDepth_3704_ = lean_ctor_get(v___y_3671_, 5);
v_customCanUnfoldPredicate_x3f_3705_ = lean_ctor_get(v___y_3671_, 6);
v_univApprox_3706_ = lean_ctor_get_uint8(v___y_3671_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3707_ = lean_ctor_get_uint8(v___y_3671_, sizeof(void*)*7 + 2);
v_cacheInferType_3708_ = lean_ctor_get_uint8(v___y_3671_, sizeof(void*)*7 + 3);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___y_3671_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; 
v_unused_3719_ = lean_ctor_get(v___y_3671_, 0);
lean_dec(v_unused_3719_);
v___x_3710_ = v___y_3671_;
v_isShared_3711_ = v_isSharedCheck_3718_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3705_);
lean_inc(v_synthPendingDepth_3704_);
lean_inc(v_defEqCtx_x3f_3703_);
lean_inc(v_localInstances_3702_);
lean_inc(v_lctx_3701_);
lean_inc(v_zetaDeltaSet_3700_);
lean_dec(v___y_3671_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3718_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
uint64_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3712_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3698_);
v___x_3713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3713_, 0, v___x_3698_);
lean_ctor_set_uint64(v___x_3713_, sizeof(void*)*1, v___x_3712_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3713_);
v___x_3715_ = v___x_3710_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_zetaDeltaSet_3700_);
lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_lctx_3701_);
lean_ctor_set(v_reuseFailAlloc_3717_, 3, v_localInstances_3702_);
lean_ctor_set(v_reuseFailAlloc_3717_, 4, v_defEqCtx_x3f_3703_);
lean_ctor_set(v_reuseFailAlloc_3717_, 5, v_synthPendingDepth_3704_);
lean_ctor_set(v_reuseFailAlloc_3717_, 6, v_customCanUnfoldPredicate_x3f_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3717_, sizeof(void*)*7, v_trackZetaDelta_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3717_, sizeof(void*)*7 + 1, v_univApprox_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3717_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3717_, sizeof(void*)*7 + 3, v_cacheInferType_3708_);
v___x_3715_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; 
v___x_3716_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3670_, v___x_3715_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec_ref(v___x_3715_);
return v___x_3716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v___y_3751_; lean_object* v_toCold_3768_; lean_object* v_currRecDepth_3769_; lean_object* v_ref_3770_; uint16_t v_optionFlags_3771_; uint8_t v_suppressElabErrors_3772_; uint8_t v_checkDeprecated_3773_; uint8_t v_isRecordingDeps_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3814_; 
v_toCold_3768_ = lean_ctor_get(v_a_3747_, 0);
v_currRecDepth_3769_ = lean_ctor_get(v_a_3747_, 1);
v_ref_3770_ = lean_ctor_get(v_a_3747_, 2);
v_optionFlags_3771_ = lean_ctor_get_uint16(v_a_3747_, sizeof(void*)*3);
v_suppressElabErrors_3772_ = lean_ctor_get_uint8(v_a_3747_, sizeof(void*)*3 + 2);
v_checkDeprecated_3773_ = lean_ctor_get_uint8(v_a_3747_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3774_ = lean_ctor_get_uint8(v_a_3747_, sizeof(void*)*3 + 4);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_a_3747_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3776_ = v_a_3747_;
v_isShared_3777_ = v_isSharedCheck_3814_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_ref_3770_);
lean_inc(v_currRecDepth_3769_);
lean_inc(v_toCold_3768_);
lean_dec(v_a_3747_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3814_;
goto v_resetjp_3775_;
}
v___jp_3750_:
{
if (lean_obj_tag(v___y_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_a_3752_ = lean_ctor_get(v___y_3751_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___y_3751_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___y_3751_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___y_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_a_3760_ = lean_ctor_get(v___y_3751_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___y_3751_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___y_3751_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___y_3751_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
v_resetjp_3775_:
{
lean_object* v_maxRecDepth_3778_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_maxRecDepth_3778_ = lean_ctor_get(v_toCold_3768_, 3);
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3811_ = lean_nat_dec_eq(v_maxRecDepth_3778_, v___x_3810_);
if (v___x_3811_ == 0)
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_nat_dec_eq(v_currRecDepth_3769_, v_maxRecDepth_3778_);
if (v___x_3812_ == 0)
{
goto v___jp_3779_;
}
else
{
lean_object* v___x_3813_; 
lean_del_object(v___x_3776_);
lean_dec(v_currRecDepth_3769_);
lean_dec_ref(v_toCold_3768_);
lean_dec(v_a_3748_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec_ref(v_e_3744_);
v___x_3813_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3770_);
return v___x_3813_;
}
}
else
{
goto v___jp_3779_;
}
v___jp_3779_:
{
lean_object* v___x_3780_; uint8_t v_transparency_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3780_ = l_Lean_Meta_Context_config(v_a_3745_);
v_transparency_3781_ = lean_ctor_get_uint8(v___x_3780_, 9);
lean_dec_ref(v___x_3780_);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = lean_nat_add(v_currRecDepth_3769_, v___x_3782_);
lean_dec(v_currRecDepth_3769_);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 1, v___x_3783_);
v___x_3785_ = v___x_3776_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_toCold_3768_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3809_, 2, v_ref_3770_);
lean_ctor_set_uint16(v_reuseFailAlloc_3809_, sizeof(void*)*3, v_optionFlags_3771_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, sizeof(void*)*3 + 2, v_suppressElabErrors_3772_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, sizeof(void*)*3 + 3, v_checkDeprecated_3773_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, sizeof(void*)*3 + 4, v_isRecordingDeps_3774_);
v___x_3785_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
uint8_t v___x_3786_; uint8_t v___x_3787_; 
v___x_3786_ = 1;
v___x_3787_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3781_, v___x_3786_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3744_, v_a_3745_, v_a_3746_, v___x_3785_, v_a_3748_);
lean_dec(v_a_3748_);
lean_dec_ref(v___x_3785_);
lean_dec(v_a_3746_);
v___y_3751_ = v___x_3788_;
goto v___jp_3750_;
}
else
{
lean_object* v_keyedConfig_3789_; uint8_t v_trackZetaDelta_3790_; lean_object* v_zetaDeltaSet_3791_; lean_object* v_lctx_3792_; lean_object* v_localInstances_3793_; lean_object* v_defEqCtx_x3f_3794_; lean_object* v_synthPendingDepth_3795_; lean_object* v_customCanUnfoldPredicate_x3f_3796_; uint8_t v_univApprox_3797_; uint8_t v_inTypeClassResolution_3798_; uint8_t v_cacheInferType_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3808_; 
v_keyedConfig_3789_ = lean_ctor_get(v_a_3745_, 0);
v_trackZetaDelta_3790_ = lean_ctor_get_uint8(v_a_3745_, sizeof(void*)*7);
v_zetaDeltaSet_3791_ = lean_ctor_get(v_a_3745_, 1);
v_lctx_3792_ = lean_ctor_get(v_a_3745_, 2);
v_localInstances_3793_ = lean_ctor_get(v_a_3745_, 3);
v_defEqCtx_x3f_3794_ = lean_ctor_get(v_a_3745_, 4);
v_synthPendingDepth_3795_ = lean_ctor_get(v_a_3745_, 5);
v_customCanUnfoldPredicate_x3f_3796_ = lean_ctor_get(v_a_3745_, 6);
v_univApprox_3797_ = lean_ctor_get_uint8(v_a_3745_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3798_ = lean_ctor_get_uint8(v_a_3745_, sizeof(void*)*7 + 2);
v_cacheInferType_3799_ = lean_ctor_get_uint8(v_a_3745_, sizeof(void*)*7 + 3);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_a_3745_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3801_ = v_a_3745_;
v_isShared_3802_ = v_isSharedCheck_3808_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3796_);
lean_inc(v_synthPendingDepth_3795_);
lean_inc(v_defEqCtx_x3f_3794_);
lean_inc(v_localInstances_3793_);
lean_inc(v_lctx_3792_);
lean_inc(v_zetaDeltaSet_3791_);
lean_inc(v_keyedConfig_3789_);
lean_dec(v_a_3745_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3808_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3786_, v_keyedConfig_3789_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3803_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_zetaDeltaSet_3791_);
lean_ctor_set(v_reuseFailAlloc_3807_, 2, v_lctx_3792_);
lean_ctor_set(v_reuseFailAlloc_3807_, 3, v_localInstances_3793_);
lean_ctor_set(v_reuseFailAlloc_3807_, 4, v_defEqCtx_x3f_3794_);
lean_ctor_set(v_reuseFailAlloc_3807_, 5, v_synthPendingDepth_3795_);
lean_ctor_set(v_reuseFailAlloc_3807_, 6, v_customCanUnfoldPredicate_x3f_3796_);
lean_ctor_set_uint8(v_reuseFailAlloc_3807_, sizeof(void*)*7, v_trackZetaDelta_3790_);
lean_ctor_set_uint8(v_reuseFailAlloc_3807_, sizeof(void*)*7 + 1, v_univApprox_3797_);
lean_ctor_set_uint8(v_reuseFailAlloc_3807_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3798_);
lean_ctor_set_uint8(v_reuseFailAlloc_3807_, sizeof(void*)*7 + 3, v_cacheInferType_3799_);
v___x_3805_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3744_, v___x_3805_, v_a_3746_, v___x_3785_, v_a_3748_);
lean_dec(v_a_3748_);
lean_dec_ref(v___x_3785_);
lean_dec(v_a_3746_);
v___y_3751_ = v___x_3806_;
goto v___jp_3750_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = lean_infer_type(v_e_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
return v_res_3821_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3822_){
_start:
{
switch(lean_obj_tag(v_x_3822_))
{
case 0:
{
uint8_t v___x_3823_; 
v___x_3823_ = 1;
return v___x_3823_;
}
case 2:
{
lean_object* v_a_3824_; lean_object* v_a_3825_; uint8_t v___x_3826_; 
v_a_3824_ = lean_ctor_get(v_x_3822_, 0);
v_a_3825_ = lean_ctor_get(v_x_3822_, 1);
v___x_3826_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3824_);
if (v___x_3826_ == 0)
{
return v___x_3826_;
}
else
{
v_x_3822_ = v_a_3825_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3828_; 
v_a_3828_ = lean_ctor_get(v_x_3822_, 1);
v_x_3822_ = v_a_3828_;
goto _start;
}
default: 
{
uint8_t v___x_3830_; 
v___x_3830_ = 0;
return v___x_3830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3831_){
_start:
{
uint8_t v_res_3832_; lean_object* v_r_3833_; 
v_res_3832_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3831_);
lean_dec(v_x_3831_);
v_r_3833_ = lean_box(v_res_3832_);
return v_r_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v___x_3837_; lean_object* v_mctx_3838_; lean_object* v___x_3839_; lean_object* v_fst_3840_; lean_object* v_snd_3841_; lean_object* v___x_3842_; lean_object* v_cache_3843_; lean_object* v_zetaDeltaFVarIds_3844_; lean_object* v_postponed_3845_; lean_object* v_diag_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3855_; 
v___x_3837_ = lean_st_ref_get(v___y_3835_);
v_mctx_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc_ref(v_mctx_3838_);
lean_dec(v___x_3837_);
v___x_3839_ = lean_instantiate_level_mvars(v_mctx_3838_, v_l_3834_);
v_fst_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_fst_3840_);
v_snd_3841_ = lean_ctor_get(v___x_3839_, 1);
lean_inc(v_snd_3841_);
lean_dec_ref(v___x_3839_);
v___x_3842_ = lean_st_ref_take(v___y_3835_);
v_cache_3843_ = lean_ctor_get(v___x_3842_, 1);
v_zetaDeltaFVarIds_3844_ = lean_ctor_get(v___x_3842_, 2);
v_postponed_3845_ = lean_ctor_get(v___x_3842_, 3);
v_diag_3846_ = lean_ctor_get(v___x_3842_, 4);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3855_ == 0)
{
lean_object* v_unused_3856_; 
v_unused_3856_ = lean_ctor_get(v___x_3842_, 0);
lean_dec(v_unused_3856_);
v___x_3848_ = v___x_3842_;
v_isShared_3849_ = v_isSharedCheck_3855_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_diag_3846_);
lean_inc(v_postponed_3845_);
lean_inc(v_zetaDeltaFVarIds_3844_);
lean_inc(v_cache_3843_);
lean_dec(v___x_3842_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3855_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v_fst_3840_);
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_fst_3840_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_cache_3843_);
lean_ctor_set(v_reuseFailAlloc_3854_, 2, v_zetaDeltaFVarIds_3844_);
lean_ctor_set(v_reuseFailAlloc_3854_, 3, v_postponed_3845_);
lean_ctor_set(v_reuseFailAlloc_3854_, 4, v_diag_3846_);
v___x_3851_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_st_ref_put(v___y_3835_, v___x_3851_);
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_snd_3841_);
return v___x_3853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3857_, v___y_3858_);
lean_dec(v___y_3858_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3861_, v___y_3863_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3875_, lean_object* v_x_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
switch(lean_obj_tag(v_x_3875_))
{
case 3:
{
lean_object* v_u_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v_u_3886_ = lean_ctor_get(v_x_3875_, 0);
lean_inc(v_u_3886_);
lean_dec_ref_known(v_x_3875_, 1);
v___x_3887_ = lean_unsigned_to_nat(0u);
v___x_3888_ = lean_nat_dec_eq(v_x_3876_, v___x_3887_);
lean_dec(v_x_3876_);
if (v___x_3888_ == 0)
{
lean_dec(v_u_3886_);
goto v___jp_3882_;
}
else
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3886_, v_a_3878_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3900_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3900_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3900_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
uint8_t v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3894_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3890_);
lean_dec(v_a_3890_);
v___x_3895_ = l_Lean_Bool_toLBool(v___x_3894_);
v___x_3896_ = lean_box(v___x_3895_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3896_);
v___x_3898_ = v___x_3892_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
v_a_3901_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3889_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3889_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3909_; lean_object* v_zero_3910_; uint8_t v_isZero_3911_; 
v_body_3909_ = lean_ctor_get(v_x_3875_, 2);
lean_inc_ref(v_body_3909_);
lean_dec_ref_known(v_x_3875_, 3);
v_zero_3910_ = lean_unsigned_to_nat(0u);
v_isZero_3911_ = lean_nat_dec_eq(v_x_3876_, v_zero_3910_);
if (v_isZero_3911_ == 1)
{
uint8_t v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_dec_ref(v_body_3909_);
lean_dec(v_x_3876_);
v___x_3912_ = 0;
v___x_3913_ = lean_box(v___x_3912_);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
return v___x_3914_;
}
else
{
lean_object* v_one_3915_; lean_object* v_n_3916_; 
v_one_3915_ = lean_unsigned_to_nat(1u);
v_n_3916_ = lean_nat_sub(v_x_3876_, v_one_3915_);
lean_dec(v_x_3876_);
v_x_3875_ = v_body_3909_;
v_x_3876_ = v_n_3916_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3918_; 
v_body_3918_ = lean_ctor_get(v_x_3875_, 3);
lean_inc_ref(v_body_3918_);
lean_dec_ref_known(v_x_3875_, 4);
v_x_3875_ = v_body_3918_;
goto _start;
}
case 10:
{
lean_object* v_expr_3920_; 
v_expr_3920_ = lean_ctor_get(v_x_3875_, 1);
lean_inc_ref(v_expr_3920_);
lean_dec_ref_known(v_x_3875_, 2);
v_x_3875_ = v_expr_3920_;
goto _start;
}
default: 
{
lean_dec(v_x_3876_);
lean_dec_ref(v_x_3875_);
goto v___jp_3882_;
}
}
v___jp_3882_:
{
uint8_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3883_ = 2;
v___x_3884_ = lean_box(v___x_3883_);
v___x_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
return v___x_3885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3922_, lean_object* v_x_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3922_, v_x_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3930_, lean_object* v_x_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
switch(lean_obj_tag(v_x_3930_))
{
case 4:
{
lean_object* v_declName_3937_; lean_object* v_us_3938_; lean_object* v___x_3939_; 
v_declName_3937_ = lean_ctor_get(v_x_3930_, 0);
lean_inc(v_declName_3937_);
v_us_3938_ = lean_ctor_get(v_x_3930_, 1);
lean_inc(v_us_3938_);
lean_dec_ref_known(v_x_3930_, 2);
v___x_3939_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3937_, v_us_3938_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3941_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v___x_3941_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3940_, v_x_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
return v___x_3941_;
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec(v_x_3931_);
v_a_3942_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3939_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3939_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3950_; lean_object* v___x_3951_; 
v_fvarId_3950_ = lean_ctor_get(v_x_3930_, 0);
lean_inc(v_fvarId_3950_);
lean_dec_ref_known(v_x_3930_, 1);
v___x_3951_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3950_, v_a_3932_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3952_, v_x_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
return v___x_3953_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_x_3931_);
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
case 2:
{
lean_object* v_mvarId_3962_; lean_object* v___x_3963_; 
v_mvarId_3962_ = lean_ctor_get(v_x_3930_, 0);
lean_inc(v_mvarId_3962_);
lean_dec_ref_known(v_x_3930_, 1);
v___x_3963_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3962_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3964_, v_x_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
return v___x_3965_;
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v_x_3931_);
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
case 5:
{
lean_object* v_fn_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_fn_3974_ = lean_ctor_get(v_x_3930_, 0);
lean_inc_ref(v_fn_3974_);
lean_dec_ref_known(v_x_3930_, 2);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_nat_add(v_x_3931_, v___x_3975_);
lean_dec(v_x_3931_);
v_x_3930_ = v_fn_3974_;
v_x_3931_ = v___x_3976_;
goto _start;
}
case 10:
{
lean_object* v_expr_3978_; 
v_expr_3978_ = lean_ctor_get(v_x_3930_, 1);
lean_inc_ref(v_expr_3978_);
lean_dec_ref_known(v_x_3930_, 2);
v_x_3930_ = v_expr_3978_;
goto _start;
}
case 8:
{
lean_object* v_body_3980_; 
v_body_3980_ = lean_ctor_get(v_x_3930_, 3);
lean_inc_ref(v_body_3980_);
lean_dec_ref_known(v_x_3930_, 4);
v_x_3930_ = v_body_3980_;
goto _start;
}
case 6:
{
lean_object* v_body_3982_; lean_object* v_zero_3983_; uint8_t v_isZero_3984_; 
v_body_3982_ = lean_ctor_get(v_x_3930_, 2);
lean_inc_ref(v_body_3982_);
lean_dec_ref_known(v_x_3930_, 3);
v_zero_3983_ = lean_unsigned_to_nat(0u);
v_isZero_3984_ = lean_nat_dec_eq(v_x_3931_, v_zero_3983_);
if (v_isZero_3984_ == 1)
{
uint8_t v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
lean_dec_ref(v_body_3982_);
lean_dec(v_x_3931_);
v___x_3985_ = 0;
v___x_3986_ = lean_box(v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
return v___x_3987_;
}
else
{
lean_object* v_one_3988_; lean_object* v_n_3989_; 
v_one_3988_ = lean_unsigned_to_nat(1u);
v_n_3989_ = lean_nat_sub(v_x_3931_, v_one_3988_);
lean_dec(v_x_3931_);
v_x_3930_ = v_body_3982_;
v_x_3931_ = v_n_3989_;
goto _start;
}
}
default: 
{
uint8_t v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
lean_dec(v_x_3931_);
lean_dec_ref(v_x_3930_);
v___x_3991_ = 2;
v___x_3992_ = lean_box(v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
return v___x_3993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3994_, v_x_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
switch(lean_obj_tag(v_x_4002_))
{
case 1:
{
lean_object* v_fvarId_4008_; lean_object* v___x_4009_; 
v_fvarId_4008_ = lean_ctor_get(v_x_4002_, 0);
lean_inc(v_fvarId_4008_);
lean_dec_ref_known(v_x_4002_, 1);
v___x_4009_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4008_, v_a_4003_, v_a_4005_, v_a_4006_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v___x_4011_ = lean_unsigned_to_nat(0u);
v___x_4012_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4010_, v___x_4011_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
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
case 2:
{
lean_object* v_mvarId_4021_; lean_object* v___x_4022_; 
v_mvarId_4021_ = lean_ctor_get(v_x_4002_, 0);
lean_inc(v_mvarId_4021_);
lean_dec_ref_known(v_x_4002_, 1);
v___x_4022_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4021_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4022_, 1);
v___x_4024_ = lean_unsigned_to_nat(0u);
v___x_4025_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4023_, v___x_4024_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
return v___x_4025_;
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
v_a_4026_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_4022_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4022_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
case 3:
{
uint8_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_dec_ref_known(v_x_4002_, 1);
v___x_4034_ = 0;
v___x_4035_ = lean_box(v___x_4034_);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
case 4:
{
lean_object* v_declName_4037_; lean_object* v_us_4038_; lean_object* v___x_4039_; 
v_declName_4037_ = lean_ctor_get(v_x_4002_, 0);
lean_inc(v_declName_4037_);
v_us_4038_ = lean_ctor_get(v_x_4002_, 1);
lean_inc(v_us_4038_);
lean_dec_ref_known(v_x_4002_, 2);
v___x_4039_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4037_, v_us_4038_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4039_, 1);
v___x_4041_ = lean_unsigned_to_nat(0u);
v___x_4042_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4040_, v___x_4041_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
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
case 5:
{
lean_object* v_fn_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v_fn_4051_ = lean_ctor_get(v_x_4002_, 0);
lean_inc_ref(v_fn_4051_);
lean_dec_ref_known(v_x_4002_, 2);
v___x_4052_ = lean_unsigned_to_nat(1u);
v___x_4053_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4051_, v___x_4052_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
return v___x_4053_;
}
case 6:
{
uint8_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
lean_dec_ref_known(v_x_4002_, 3);
v___x_4054_ = 0;
v___x_4055_ = lean_box(v___x_4054_);
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
case 7:
{
lean_object* v_body_4057_; 
v_body_4057_ = lean_ctor_get(v_x_4002_, 2);
lean_inc_ref(v_body_4057_);
lean_dec_ref_known(v_x_4002_, 3);
v_x_4002_ = v_body_4057_;
goto _start;
}
case 8:
{
lean_object* v_body_4059_; 
v_body_4059_ = lean_ctor_get(v_x_4002_, 3);
lean_inc_ref(v_body_4059_);
lean_dec_ref_known(v_x_4002_, 4);
v_x_4002_ = v_body_4059_;
goto _start;
}
case 9:
{
uint8_t v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
lean_dec_ref_known(v_x_4002_, 1);
v___x_4061_ = 0;
v___x_4062_ = lean_box(v___x_4061_);
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
return v___x_4063_;
}
case 10:
{
lean_object* v_expr_4064_; 
v_expr_4064_ = lean_ctor_get(v_x_4002_, 1);
lean_inc_ref(v_expr_4064_);
lean_dec_ref_known(v_x_4002_, 2);
v_x_4002_ = v_expr_4064_;
goto _start;
}
default: 
{
uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec_ref(v_x_4002_);
v___x_4066_ = 2;
v___x_4067_ = lean_box(v___x_4066_);
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_Meta_isPropQuick(v_x_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v___x_4082_; 
lean_inc_ref(v_e_4076_);
v___x_4082_ = l_Lean_Meta_isPropQuick(v_e_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4139_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4139_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4139_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
uint8_t v___x_4087_; 
v___x_4087_ = lean_unbox(v_a_4083_);
lean_dec(v_a_4083_);
switch(v___x_4087_)
{
case 0:
{
uint8_t v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4091_; 
lean_dec_ref(v_e_4076_);
v___x_4088_ = 0;
v___x_4089_ = lean_box(v___x_4088_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4089_);
v___x_4091_ = v___x_4085_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
case 1:
{
uint8_t v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4096_; 
lean_dec_ref(v_e_4076_);
v___x_4093_ = 1;
v___x_4094_ = lean_box(v___x_4093_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4094_);
v___x_4096_ = v___x_4085_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4094_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
default: 
{
lean_object* v___x_4098_; 
lean_del_object(v___x_4085_);
lean_inc(v_a_4080_);
lean_inc_ref(v_a_4079_);
lean_inc(v_a_4078_);
lean_inc_ref(v_a_4077_);
v___x_4098_ = lean_infer_type(v_e_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v___x_4100_ = l_Lean_Meta_whnfD(v_a_4099_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4122_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4122_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4122_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
if (lean_obj_tag(v_a_4101_) == 3)
{
lean_object* v_u_4105_; lean_object* v___x_4106_; lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4116_; 
lean_del_object(v___x_4103_);
v_u_4105_ = lean_ctor_get(v_a_4101_, 0);
lean_inc(v_u_4105_);
lean_dec_ref_known(v_a_4101_, 1);
v___x_4106_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4105_, v_a_4078_);
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4116_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4111_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4107_);
lean_dec(v_a_4107_);
v___x_4112_ = lean_box(v___x_4111_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v___x_4112_);
v___x_4114_ = v___x_4109_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
else
{
uint8_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
lean_dec(v_a_4101_);
v___x_4117_ = 0;
v___x_4118_ = lean_box(v___x_4117_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4118_);
v___x_4120_ = v___x_4103_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4118_);
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
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
v_a_4123_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4100_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4100_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
v_a_4131_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4098_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4098_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v_e_4076_);
v_a_4140_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4082_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4082_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_Meta_isProp(v_e_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
lean_dec(v_a_4152_);
lean_dec_ref(v_a_4151_);
lean_dec(v_a_4150_);
lean_dec_ref(v_a_4149_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4155_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = lean_obj_tag_nat(v_x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4157_);
lean_dec(v_x_4157_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4159_, lean_object* v_k_4160_){
_start:
{
if (lean_obj_tag(v_t_4159_) == 3)
{
lean_object* v_idx_4161_; lean_object* v_numArgs_4162_; lean_object* v___x_4163_; 
v_idx_4161_ = lean_ctor_get(v_t_4159_, 0);
lean_inc(v_idx_4161_);
v_numArgs_4162_ = lean_ctor_get(v_t_4159_, 1);
lean_inc(v_numArgs_4162_);
lean_dec_ref_known(v_t_4159_, 2);
v___x_4163_ = lean_apply_2(v_k_4160_, v_idx_4161_, v_numArgs_4162_);
return v___x_4163_;
}
else
{
lean_dec(v_t_4159_);
return v_k_4160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4164_, lean_object* v_ctorIdx_4165_, lean_object* v_t_4166_, lean_object* v_h_4167_, lean_object* v_k_4168_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4166_, v_k_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4170_, lean_object* v_ctorIdx_4171_, lean_object* v_t_4172_, lean_object* v_h_4173_, lean_object* v_k_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4170_, v_ctorIdx_4171_, v_t_4172_, v_h_4173_, v_k_4174_);
lean_dec(v_ctorIdx_4171_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4176_, lean_object* v_false_4177_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4176_, v_false_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4179_, lean_object* v_t_4180_, lean_object* v_h_4181_, lean_object* v_false_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4180_, v_false_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4184_, lean_object* v_true_4185_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4184_, v_true_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4187_, lean_object* v_t_4188_, lean_object* v_h_4189_, lean_object* v_true_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4188_, v_true_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4192_, lean_object* v_undef_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4192_, v_undef_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4195_, lean_object* v_t_4196_, lean_object* v_h_4197_, lean_object* v_undef_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4196_, v_undef_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4200_, lean_object* v_bvar_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4200_, v_bvar_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4203_, lean_object* v_t_4204_, lean_object* v_h_4205_, lean_object* v_bvar_4206_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4204_, v_bvar_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4208_){
_start:
{
switch(v_x_4208_)
{
case 0:
{
lean_object* v___x_4209_; 
v___x_4209_ = lean_box(0);
return v___x_4209_;
}
case 1:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_box(1);
return v___x_4210_;
}
default: 
{
lean_object* v___x_4211_; 
v___x_4211_ = lean_box(2);
return v___x_4211_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4212_){
_start:
{
uint8_t v_x_25__boxed_4213_; lean_object* v_res_4214_; 
v_x_25__boxed_4213_ = lean_unbox(v_x_4212_);
v_res_4214_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4213_);
return v_res_4214_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4215_){
_start:
{
switch(lean_obj_tag(v_x_4215_))
{
case 0:
{
uint8_t v___x_4216_; 
v___x_4216_ = 0;
return v___x_4216_;
}
case 1:
{
uint8_t v___x_4217_; 
v___x_4217_ = 1;
return v___x_4217_;
}
default: 
{
uint8_t v___x_4218_; 
v___x_4218_ = 2;
return v___x_4218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4219_){
_start:
{
uint8_t v_res_4220_; lean_object* v_r_4221_; 
v_res_4220_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4219_);
lean_dec(v_x_4219_);
v_r_4221_ = lean_box(v_res_4220_);
return v_r_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4223_, lean_object* v_numArgs_4224_){
_start:
{
switch(lean_obj_tag(v_e_4223_))
{
case 3:
{
lean_object* v_u_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; 
v_u_4225_ = lean_ctor_get(v_e_4223_, 0);
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = lean_nat_dec_eq(v_numArgs_4224_, v___x_4226_);
lean_dec(v_numArgs_4224_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_box(2);
return v___x_4228_;
}
else
{
uint8_t v___x_4229_; 
v___x_4229_ = l_Lean_Level_isNeverZero(v_u_4225_);
if (v___x_4229_ == 0)
{
uint8_t v___x_4230_; 
v___x_4230_ = l_Lean_Level_isZero(v_u_4225_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_box(2);
return v___x_4231_;
}
else
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_box(1);
return v___x_4232_;
}
}
else
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_box(0);
return v___x_4233_;
}
}
}
case 7:
{
lean_object* v_body_4234_; lean_object* v_zero_4235_; uint8_t v_isZero_4236_; 
v_body_4234_ = lean_ctor_get(v_e_4223_, 2);
v_zero_4235_ = lean_unsigned_to_nat(0u);
v_isZero_4236_ = lean_nat_dec_eq(v_numArgs_4224_, v_zero_4235_);
if (v_isZero_4236_ == 0)
{
lean_object* v_one_4237_; lean_object* v_n_4238_; 
v_one_4237_ = lean_unsigned_to_nat(1u);
v_n_4238_ = lean_nat_sub(v_numArgs_4224_, v_one_4237_);
lean_dec(v_numArgs_4224_);
v_e_4223_ = v_body_4234_;
v_numArgs_4224_ = v_n_4238_;
goto _start;
}
else
{
lean_object* v___x_4240_; 
lean_dec(v_numArgs_4224_);
v___x_4240_ = lean_box(2);
return v___x_4240_;
}
}
case 10:
{
lean_object* v_expr_4241_; 
v_expr_4241_ = lean_ctor_get(v_e_4223_, 1);
v_e_4223_ = v_expr_4241_;
goto _start;
}
case 5:
{
lean_object* v_fn_4243_; 
v_fn_4243_ = lean_ctor_get(v_e_4223_, 0);
if (lean_obj_tag(v_fn_4243_) == 4)
{
lean_object* v_declName_4244_; 
v_declName_4244_ = lean_ctor_get(v_fn_4243_, 0);
if (lean_obj_tag(v_declName_4244_) == 1)
{
lean_object* v_pre_4245_; 
v_pre_4245_ = lean_ctor_get(v_declName_4244_, 0);
if (lean_obj_tag(v_pre_4245_) == 0)
{
lean_object* v_arg_4246_; lean_object* v_str_4247_; lean_object* v___x_4248_; uint8_t v___x_4249_; 
v_arg_4246_ = lean_ctor_get(v_e_4223_, 1);
v_str_4247_ = lean_ctor_get(v_declName_4244_, 1);
v___x_4248_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4249_ = lean_string_dec_eq(v_str_4247_, v___x_4248_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4250_; 
lean_dec(v_numArgs_4224_);
v___x_4250_ = lean_box(2);
return v___x_4250_;
}
else
{
v_e_4223_ = v_arg_4246_;
goto _start;
}
}
else
{
lean_object* v___x_4252_; 
lean_dec(v_numArgs_4224_);
v___x_4252_ = lean_box(2);
return v___x_4252_;
}
}
else
{
lean_object* v___x_4253_; 
lean_dec(v_numArgs_4224_);
v___x_4253_ = lean_box(2);
return v___x_4253_;
}
}
else
{
lean_object* v___x_4254_; 
lean_dec(v_numArgs_4224_);
v___x_4254_ = lean_box(2);
return v___x_4254_;
}
}
default: 
{
lean_object* v___x_4255_; 
lean_dec(v_numArgs_4224_);
v___x_4255_ = lean_box(2);
return v___x_4255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4256_, lean_object* v_numArgs_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4256_, v_numArgs_4257_);
lean_dec_ref(v_e_4256_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4259_, lean_object* v_binderType_4260_){
_start:
{
if (lean_obj_tag(v_r_4259_) == 3)
{
lean_object* v_idx_4261_; lean_object* v_numArgs_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4274_; 
v_idx_4261_ = lean_ctor_get(v_r_4259_, 0);
v_numArgs_4262_ = lean_ctor_get(v_r_4259_, 1);
v_isSharedCheck_4274_ = !lean_is_exclusive(v_r_4259_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4264_ = v_r_4259_;
v_isShared_4265_ = v_isSharedCheck_4274_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_numArgs_4262_);
lean_inc(v_idx_4261_);
lean_dec(v_r_4259_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4274_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v_zero_4266_; uint8_t v_isZero_4267_; 
v_zero_4266_ = lean_unsigned_to_nat(0u);
v_isZero_4267_ = lean_nat_dec_eq(v_idx_4261_, v_zero_4266_);
if (v_isZero_4267_ == 1)
{
lean_object* v___x_4268_; 
lean_del_object(v___x_4264_);
lean_dec(v_idx_4261_);
v___x_4268_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4260_, v_numArgs_4262_);
return v___x_4268_;
}
else
{
lean_object* v_one_4269_; lean_object* v_n_4270_; lean_object* v___x_4272_; 
v_one_4269_ = lean_unsigned_to_nat(1u);
v_n_4270_ = lean_nat_sub(v_idx_4261_, v_one_4269_);
lean_dec(v_idx_4261_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v_n_4270_);
v___x_4272_ = v___x_4264_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_n_4270_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_numArgs_4262_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
return v_r_4259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4275_, lean_object* v_binderType_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4275_, v_binderType_4276_);
lean_dec_ref(v_binderType_4276_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4278_, lean_object* v_x_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_type_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; 
switch(lean_obj_tag(v_x_4278_))
{
case 7:
{
lean_object* v_binderType_4318_; lean_object* v_body_4319_; lean_object* v_zero_4320_; uint8_t v_isZero_4321_; 
v_binderType_4318_ = lean_ctor_get(v_x_4278_, 1);
v_body_4319_ = lean_ctor_get(v_x_4278_, 2);
v_zero_4320_ = lean_unsigned_to_nat(0u);
v_isZero_4321_ = lean_nat_dec_eq(v_x_4279_, v_zero_4320_);
if (v_isZero_4321_ == 1)
{
v_type_4286_ = v_x_4278_;
v___y_4287_ = v_a_4280_;
v___y_4288_ = v_a_4281_;
v___y_4289_ = v_a_4282_;
v___y_4290_ = v_a_4283_;
goto v___jp_4285_;
}
else
{
lean_object* v_one_4322_; lean_object* v_n_4323_; lean_object* v___x_4324_; 
lean_inc_ref(v_body_4319_);
lean_inc_ref(v_binderType_4318_);
lean_dec_ref_known(v_x_4278_, 3);
v_one_4322_ = lean_unsigned_to_nat(1u);
v_n_4323_ = lean_nat_sub(v_x_4279_, v_one_4322_);
v___x_4324_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4319_, v_n_4323_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
lean_dec(v_n_4323_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4333_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4333_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4331_; 
v___x_4329_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4325_, v_binderType_4318_);
lean_dec_ref(v_binderType_4318_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4329_);
v___x_4331_ = v___x_4327_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4329_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
lean_dec_ref(v_binderType_4318_);
return v___x_4324_;
}
}
}
case 8:
{
lean_object* v_type_4334_; lean_object* v_body_4335_; lean_object* v___x_4336_; 
v_type_4334_ = lean_ctor_get(v_x_4278_, 1);
lean_inc_ref(v_type_4334_);
v_body_4335_ = lean_ctor_get(v_x_4278_, 3);
lean_inc_ref(v_body_4335_);
lean_dec_ref_known(v_x_4278_, 4);
v___x_4336_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4335_, v_x_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4345_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4341_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4337_, v_type_4334_);
lean_dec_ref(v_type_4334_);
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v___x_4341_);
v___x_4343_ = v___x_4339_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
else
{
lean_dec_ref(v_type_4334_);
return v___x_4336_;
}
}
case 10:
{
lean_object* v_expr_4346_; 
v_expr_4346_ = lean_ctor_get(v_x_4278_, 1);
lean_inc_ref(v_expr_4346_);
lean_dec_ref_known(v_x_4278_, 2);
v_x_4278_ = v_expr_4346_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4348_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
v_deBruijnIndex_4348_ = lean_ctor_get(v_x_4278_, 0);
lean_inc(v_deBruijnIndex_4348_);
lean_dec_ref_known(v_x_4278_, 1);
v___x_4349_ = lean_unsigned_to_nat(0u);
v___x_4350_ = lean_nat_dec_eq(v_x_4279_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_dec(v_deBruijnIndex_4348_);
goto v___jp_4315_;
}
else
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4351_, 0, v_deBruijnIndex_4348_);
lean_ctor_set(v___x_4351_, 1, v___x_4349_);
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
return v___x_4352_;
}
}
default: 
{
lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4353_ = lean_unsigned_to_nat(0u);
v___x_4354_ = lean_nat_dec_eq(v_x_4279_, v___x_4353_);
if (v___x_4354_ == 0)
{
lean_dec_ref(v_x_4278_);
goto v___jp_4315_;
}
else
{
v_type_4286_ = v_x_4278_;
v___y_4287_ = v_a_4280_;
v___y_4288_ = v_a_4281_;
v___y_4289_ = v_a_4282_;
v___y_4290_ = v_a_4283_;
goto v___jp_4285_;
}
}
}
v___jp_4285_:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Expr_getAppFn(v_type_4286_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_deBruijnIndex_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_deBruijnIndex_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_deBruijnIndex_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = l_Lean_Expr_getAppNumArgs(v_type_4286_);
lean_dec_ref(v_type_4286_);
v___x_4294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4294_, 0, v_deBruijnIndex_4292_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
return v___x_4295_;
}
else
{
lean_object* v___x_4296_; 
lean_dec_ref(v___x_4291_);
v___x_4296_ = l_Lean_Meta_isPropQuick(v_type_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4306_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4306_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4306_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
uint8_t v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4301_ = lean_unbox(v_a_4297_);
lean_dec(v_a_4297_);
v___x_4302_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4301_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4302_);
v___x_4304_ = v___x_4299_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
v_a_4307_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4296_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4296_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
}
v___jp_4315_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = lean_box(2);
v___x_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
return v___x_4317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4355_, lean_object* v_x_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4355_, v_x_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
lean_dec(v_a_4360_);
lean_dec_ref(v_a_4359_);
lean_dec(v_a_4358_);
lean_dec_ref(v_a_4357_);
lean_dec(v_x_4356_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4363_, lean_object* v_n_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4363_, v_n_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4380_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4373_ = v___x_4370_;
v_isShared_4374_ = v_isSharedCheck_4380_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4380_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
uint8_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
v___x_4375_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4371_);
lean_dec(v_a_4371_);
v___x_4376_ = lean_box(v___x_4375_);
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 0, v___x_4376_);
v___x_4378_ = v___x_4373_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4376_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
v_a_4381_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4370_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4370_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4389_, lean_object* v_n_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4389_, v_n_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_n_4390_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
switch(lean_obj_tag(v_x_4397_))
{
case 1:
{
lean_object* v_fvarId_4403_; lean_object* v___x_4404_; 
v_fvarId_4403_ = lean_ctor_get(v_x_4397_, 0);
lean_inc(v_fvarId_4403_);
lean_dec_ref_known(v_x_4397_, 1);
v___x_4404_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4403_, v_a_4398_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4405_, v___x_4406_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
return v___x_4407_;
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
v_a_4408_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4404_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4404_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4416_; lean_object* v___x_4417_; 
v_mvarId_4416_ = lean_ctor_get(v_x_4397_, 0);
lean_inc(v_mvarId_4416_);
lean_dec_ref_known(v_x_4397_, 1);
v___x_4417_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4416_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v___x_4419_ = lean_unsigned_to_nat(0u);
v___x_4420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4418_, v___x_4419_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
return v___x_4420_;
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
v_a_4421_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4417_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4417_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
case 3:
{
uint8_t v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
lean_dec_ref_known(v_x_4397_, 1);
v___x_4429_ = 0;
v___x_4430_ = lean_box(v___x_4429_);
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
return v___x_4431_;
}
case 4:
{
lean_object* v_declName_4432_; lean_object* v_us_4433_; lean_object* v___x_4434_; 
v_declName_4432_ = lean_ctor_get(v_x_4397_, 0);
lean_inc(v_declName_4432_);
v_us_4433_ = lean_ctor_get(v_x_4397_, 1);
lean_inc(v_us_4433_);
lean_dec_ref_known(v_x_4397_, 2);
v___x_4434_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4432_, v_us_4433_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v_a_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_a_4435_);
lean_dec_ref_known(v___x_4434_, 1);
v___x_4436_ = lean_unsigned_to_nat(0u);
v___x_4437_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4435_, v___x_4436_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
return v___x_4437_;
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
v_a_4438_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4434_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4434_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
case 5:
{
lean_object* v_fn_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_fn_4446_ = lean_ctor_get(v_x_4397_, 0);
lean_inc_ref(v_fn_4446_);
lean_dec_ref_known(v_x_4397_, 2);
v___x_4447_ = lean_unsigned_to_nat(1u);
v___x_4448_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4446_, v___x_4447_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
return v___x_4448_;
}
case 6:
{
lean_object* v_body_4449_; 
v_body_4449_ = lean_ctor_get(v_x_4397_, 2);
lean_inc_ref(v_body_4449_);
lean_dec_ref_known(v_x_4397_, 3);
v_x_4397_ = v_body_4449_;
goto _start;
}
case 7:
{
uint8_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
lean_dec_ref_known(v_x_4397_, 3);
v___x_4451_ = 0;
v___x_4452_ = lean_box(v___x_4451_);
v___x_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
return v___x_4453_;
}
case 8:
{
lean_object* v_body_4454_; 
v_body_4454_ = lean_ctor_get(v_x_4397_, 3);
lean_inc_ref(v_body_4454_);
lean_dec_ref_known(v_x_4397_, 4);
v_x_4397_ = v_body_4454_;
goto _start;
}
case 9:
{
uint8_t v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
lean_dec_ref_known(v_x_4397_, 1);
v___x_4456_ = 0;
v___x_4457_ = lean_box(v___x_4456_);
v___x_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
return v___x_4458_;
}
case 10:
{
lean_object* v_expr_4459_; 
v_expr_4459_ = lean_ctor_get(v_x_4397_, 1);
lean_inc_ref(v_expr_4459_);
lean_dec_ref_known(v_x_4397_, 2);
v_x_4397_ = v_expr_4459_;
goto _start;
}
default: 
{
uint8_t v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
lean_dec_ref(v_x_4397_);
v___x_4461_ = 2;
v___x_4462_ = lean_box(v___x_4461_);
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
return v___x_4463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4464_, lean_object* v_x_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
switch(lean_obj_tag(v_x_4464_))
{
case 4:
{
lean_object* v_declName_4471_; lean_object* v_us_4472_; lean_object* v___x_4473_; 
v_declName_4471_ = lean_ctor_get(v_x_4464_, 0);
lean_inc(v_declName_4471_);
v_us_4472_ = lean_ctor_get(v_x_4464_, 1);
lean_inc(v_us_4472_);
lean_dec_ref_known(v_x_4464_, 2);
v___x_4473_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4471_, v_us_4472_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4475_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4474_, v_x_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_x_4465_);
return v___x_4475_;
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec(v_x_4465_);
v_a_4476_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4473_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4473_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4484_; lean_object* v___x_4485_; 
v_fvarId_4484_ = lean_ctor_get(v_x_4464_, 0);
lean_inc(v_fvarId_4484_);
lean_dec_ref_known(v_x_4464_, 1);
v___x_4485_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4484_, v_a_4466_, v_a_4468_, v_a_4469_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4487_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4487_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4486_, v_x_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_x_4465_);
return v___x_4487_;
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec(v_x_4465_);
v_a_4488_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4485_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4485_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4496_; lean_object* v___x_4497_; 
v_mvarId_4496_ = lean_ctor_get(v_x_4464_, 0);
lean_inc(v_mvarId_4496_);
lean_dec_ref_known(v_x_4464_, 1);
v___x_4497_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4496_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v___x_4499_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v___x_4499_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4498_, v_x_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_x_4465_);
return v___x_4499_;
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec(v_x_4465_);
v_a_4500_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4497_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4497_);
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
case 5:
{
lean_object* v_fn_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v_fn_4508_ = lean_ctor_get(v_x_4464_, 0);
lean_inc_ref(v_fn_4508_);
lean_dec_ref_known(v_x_4464_, 2);
v___x_4509_ = lean_unsigned_to_nat(1u);
v___x_4510_ = lean_nat_add(v_x_4465_, v___x_4509_);
lean_dec(v_x_4465_);
v_x_4464_ = v_fn_4508_;
v_x_4465_ = v___x_4510_;
goto _start;
}
case 10:
{
lean_object* v_expr_4512_; 
v_expr_4512_ = lean_ctor_get(v_x_4464_, 1);
lean_inc_ref(v_expr_4512_);
lean_dec_ref_known(v_x_4464_, 2);
v_x_4464_ = v_expr_4512_;
goto _start;
}
case 8:
{
lean_object* v_body_4514_; 
v_body_4514_ = lean_ctor_get(v_x_4464_, 3);
lean_inc_ref(v_body_4514_);
lean_dec_ref_known(v_x_4464_, 4);
v_x_4464_ = v_body_4514_;
goto _start;
}
case 6:
{
lean_object* v_body_4516_; lean_object* v_zero_4517_; uint8_t v_isZero_4518_; 
v_body_4516_ = lean_ctor_get(v_x_4464_, 2);
lean_inc_ref(v_body_4516_);
lean_dec_ref_known(v_x_4464_, 3);
v_zero_4517_ = lean_unsigned_to_nat(0u);
v_isZero_4518_ = lean_nat_dec_eq(v_x_4465_, v_zero_4517_);
if (v_isZero_4518_ == 1)
{
lean_object* v___x_4519_; 
lean_dec(v_x_4465_);
v___x_4519_ = l_Lean_Meta_isProofQuick(v_body_4516_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4519_;
}
else
{
lean_object* v_one_4520_; lean_object* v_n_4521_; 
v_one_4520_ = lean_unsigned_to_nat(1u);
v_n_4521_ = lean_nat_sub(v_x_4465_, v_one_4520_);
lean_dec(v_x_4465_);
v_x_4464_ = v_body_4516_;
v_x_4465_ = v_n_4521_;
goto _start;
}
}
default: 
{
uint8_t v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
lean_dec(v_x_4465_);
lean_dec_ref(v_x_4464_);
v___x_4523_ = 2;
v___x_4524_ = lean_box(v___x_4523_);
v___x_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
return v___x_4525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4526_, lean_object* v_x_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4526_, v_x_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_Meta_isProofQuick(v_x_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; 
lean_inc_ref(v_e_4541_);
v___x_4547_ = l_Lean_Meta_isProofQuick(v_e_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4574_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4550_ = v___x_4547_;
v_isShared_4551_ = v_isSharedCheck_4574_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4547_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4574_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
uint8_t v___x_4552_; 
v___x_4552_ = lean_unbox(v_a_4548_);
lean_dec(v_a_4548_);
switch(v___x_4552_)
{
case 0:
{
uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4556_; 
lean_dec_ref(v_e_4541_);
v___x_4553_ = 0;
v___x_4554_ = lean_box(v___x_4553_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4554_);
v___x_4556_ = v___x_4550_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
case 1:
{
uint8_t v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4561_; 
lean_dec_ref(v_e_4541_);
v___x_4558_ = 1;
v___x_4559_ = lean_box(v___x_4558_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4559_);
v___x_4561_ = v___x_4550_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4559_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
default: 
{
lean_object* v___x_4563_; 
lean_del_object(v___x_4550_);
lean_inc(v_a_4545_);
lean_inc_ref(v_a_4544_);
lean_inc(v_a_4543_);
lean_inc_ref(v_a_4542_);
v___x_4563_ = lean_infer_type(v_e_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4565_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4565_ = l_Lean_Meta_isProp(v_a_4564_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
return v___x_4565_;
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
v_a_4566_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4563_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4563_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec_ref(v_e_4541_);
v_a_4575_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4547_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4547_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l_Lean_Meta_isProof(v_e_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4590_, lean_object* v_x_4591_){
_start:
{
switch(lean_obj_tag(v_x_4590_))
{
case 3:
{
lean_object* v___x_4597_; uint8_t v___x_4598_; 
v___x_4597_ = lean_unsigned_to_nat(0u);
v___x_4598_ = lean_nat_dec_eq(v_x_4591_, v___x_4597_);
lean_dec(v_x_4591_);
if (v___x_4598_ == 0)
{
goto v___jp_4593_;
}
else
{
uint8_t v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4599_ = 1;
v___x_4600_ = lean_box(v___x_4599_);
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
return v___x_4601_;
}
}
case 7:
{
lean_object* v_body_4602_; lean_object* v_zero_4603_; uint8_t v_isZero_4604_; 
v_body_4602_ = lean_ctor_get(v_x_4590_, 2);
v_zero_4603_ = lean_unsigned_to_nat(0u);
v_isZero_4604_ = lean_nat_dec_eq(v_x_4591_, v_zero_4603_);
if (v_isZero_4604_ == 1)
{
uint8_t v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_dec(v_x_4591_);
v___x_4605_ = 0;
v___x_4606_ = lean_box(v___x_4605_);
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
return v___x_4607_;
}
else
{
lean_object* v_one_4608_; lean_object* v_n_4609_; 
v_one_4608_ = lean_unsigned_to_nat(1u);
v_n_4609_ = lean_nat_sub(v_x_4591_, v_one_4608_);
lean_dec(v_x_4591_);
v_x_4590_ = v_body_4602_;
v_x_4591_ = v_n_4609_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4611_; 
v_body_4611_ = lean_ctor_get(v_x_4590_, 3);
v_x_4590_ = v_body_4611_;
goto _start;
}
case 10:
{
lean_object* v_expr_4613_; 
v_expr_4613_ = lean_ctor_get(v_x_4590_, 1);
v_x_4590_ = v_expr_4613_;
goto _start;
}
default: 
{
lean_dec(v_x_4591_);
goto v___jp_4593_;
}
}
v___jp_4593_:
{
uint8_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = 2;
v___x_4595_ = lean_box(v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4615_, lean_object* v_x_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4615_, v_x_4616_);
lean_dec_ref(v_x_4615_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4619_, lean_object* v_x_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4619_, v_x_4620_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4627_, lean_object* v_x_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4627_, v_x_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec_ref(v_x_4627_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4635_, lean_object* v_x_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
switch(lean_obj_tag(v_x_4635_))
{
case 4:
{
lean_object* v_declName_4642_; lean_object* v_us_4643_; lean_object* v___x_4644_; 
v_declName_4642_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_declName_4642_);
v_us_4643_ = lean_ctor_get(v_x_4635_, 1);
lean_inc(v_us_4643_);
lean_dec_ref_known(v_x_4635_, 2);
v___x_4644_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4642_, v_us_4643_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4646_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v___x_4646_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4645_, v_x_4636_);
lean_dec(v_a_4645_);
return v___x_4646_;
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v_x_4636_);
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
case 1:
{
lean_object* v_fvarId_4655_; lean_object* v___x_4656_; 
v_fvarId_4655_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_fvarId_4655_);
lean_dec_ref_known(v_x_4635_, 1);
v___x_4656_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4655_, v_a_4637_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref_known(v___x_4656_, 1);
v___x_4658_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4657_, v_x_4636_);
lean_dec(v_a_4657_);
return v___x_4658_;
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_dec(v_x_4636_);
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
case 2:
{
lean_object* v_mvarId_4667_; lean_object* v___x_4668_; 
v_mvarId_4667_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_mvarId_4667_);
lean_dec_ref_known(v_x_4635_, 1);
v___x_4668_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4667_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4670_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref_known(v___x_4668_, 1);
v___x_4670_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4669_, v_x_4636_);
lean_dec(v_a_4669_);
return v___x_4670_;
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
lean_dec(v_x_4636_);
v_a_4671_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4668_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4668_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
case 5:
{
lean_object* v_fn_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v_fn_4679_ = lean_ctor_get(v_x_4635_, 0);
lean_inc_ref(v_fn_4679_);
lean_dec_ref_known(v_x_4635_, 2);
v___x_4680_ = lean_unsigned_to_nat(1u);
v___x_4681_ = lean_nat_add(v_x_4636_, v___x_4680_);
lean_dec(v_x_4636_);
v_x_4635_ = v_fn_4679_;
v_x_4636_ = v___x_4681_;
goto _start;
}
case 10:
{
lean_object* v_expr_4683_; 
v_expr_4683_ = lean_ctor_get(v_x_4635_, 1);
lean_inc_ref(v_expr_4683_);
lean_dec_ref_known(v_x_4635_, 2);
v_x_4635_ = v_expr_4683_;
goto _start;
}
case 8:
{
lean_object* v_body_4685_; 
v_body_4685_ = lean_ctor_get(v_x_4635_, 3);
lean_inc_ref(v_body_4685_);
lean_dec_ref_known(v_x_4635_, 4);
v_x_4635_ = v_body_4685_;
goto _start;
}
case 6:
{
lean_object* v_body_4687_; lean_object* v_zero_4688_; uint8_t v_isZero_4689_; 
v_body_4687_ = lean_ctor_get(v_x_4635_, 2);
lean_inc_ref(v_body_4687_);
lean_dec_ref_known(v_x_4635_, 3);
v_zero_4688_ = lean_unsigned_to_nat(0u);
v_isZero_4689_ = lean_nat_dec_eq(v_x_4636_, v_zero_4688_);
if (v_isZero_4689_ == 1)
{
uint8_t v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
lean_dec_ref(v_body_4687_);
lean_dec(v_x_4636_);
v___x_4690_ = 0;
v___x_4691_ = lean_box(v___x_4690_);
v___x_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
return v___x_4692_;
}
else
{
lean_object* v_one_4693_; lean_object* v_n_4694_; 
v_one_4693_ = lean_unsigned_to_nat(1u);
v_n_4694_ = lean_nat_sub(v_x_4636_, v_one_4693_);
lean_dec(v_x_4636_);
v_x_4635_ = v_body_4687_;
v_x_4636_ = v_n_4694_;
goto _start;
}
}
default: 
{
uint8_t v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
lean_dec(v_x_4636_);
lean_dec_ref(v_x_4635_);
v___x_4696_ = 2;
v___x_4697_ = lean_box(v___x_4696_);
v___x_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
return v___x_4698_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4699_, lean_object* v_x_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4699_, v_x_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
switch(lean_obj_tag(v_x_4707_))
{
case 1:
{
lean_object* v_fvarId_4713_; lean_object* v___x_4714_; 
v_fvarId_4713_ = lean_ctor_get(v_x_4707_, 0);
lean_inc(v_fvarId_4713_);
lean_dec_ref_known(v_x_4707_, 1);
v___x_4714_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4713_, v_a_4708_, v_a_4710_, v_a_4711_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_a_4715_);
lean_dec_ref_known(v___x_4714_, 1);
v___x_4716_ = lean_unsigned_to_nat(0u);
v___x_4717_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4715_, v___x_4716_);
lean_dec(v_a_4715_);
return v___x_4717_;
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
v_a_4718_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4714_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4714_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4726_; lean_object* v___x_4727_; 
v_mvarId_4726_ = lean_ctor_get(v_x_4707_, 0);
lean_inc(v_mvarId_4726_);
lean_dec_ref_known(v_x_4707_, 1);
v___x_4727_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4726_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v___x_4727_, 1);
v___x_4729_ = lean_unsigned_to_nat(0u);
v___x_4730_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4728_, v___x_4729_);
lean_dec(v_a_4728_);
return v___x_4730_;
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
v_a_4731_ = lean_ctor_get(v___x_4727_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4727_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4727_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
case 3:
{
uint8_t v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
lean_dec_ref_known(v_x_4707_, 1);
v___x_4739_ = 1;
v___x_4740_ = lean_box(v___x_4739_);
v___x_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
return v___x_4741_;
}
case 4:
{
lean_object* v_declName_4742_; lean_object* v_us_4743_; lean_object* v___x_4744_; 
v_declName_4742_ = lean_ctor_get(v_x_4707_, 0);
lean_inc(v_declName_4742_);
v_us_4743_ = lean_ctor_get(v_x_4707_, 1);
lean_inc(v_us_4743_);
lean_dec_ref_known(v_x_4707_, 2);
v___x_4744_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4742_, v_us_4743_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v___x_4746_ = lean_unsigned_to_nat(0u);
v___x_4747_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4745_, v___x_4746_);
lean_dec(v_a_4745_);
return v___x_4747_;
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
v_a_4748_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4744_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4744_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
case 5:
{
lean_object* v_fn_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v_fn_4756_ = lean_ctor_get(v_x_4707_, 0);
lean_inc_ref(v_fn_4756_);
lean_dec_ref_known(v_x_4707_, 2);
v___x_4757_ = lean_unsigned_to_nat(1u);
v___x_4758_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4756_, v___x_4757_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
return v___x_4758_;
}
case 6:
{
uint8_t v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_dec_ref_known(v_x_4707_, 3);
v___x_4759_ = 0;
v___x_4760_ = lean_box(v___x_4759_);
v___x_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4760_);
return v___x_4761_;
}
case 7:
{
uint8_t v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
lean_dec_ref_known(v_x_4707_, 3);
v___x_4762_ = 1;
v___x_4763_ = lean_box(v___x_4762_);
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
return v___x_4764_;
}
case 8:
{
lean_object* v_body_4765_; 
v_body_4765_ = lean_ctor_get(v_x_4707_, 3);
lean_inc_ref(v_body_4765_);
lean_dec_ref_known(v_x_4707_, 4);
v_x_4707_ = v_body_4765_;
goto _start;
}
case 9:
{
uint8_t v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
lean_dec_ref_known(v_x_4707_, 1);
v___x_4767_ = 0;
v___x_4768_ = lean_box(v___x_4767_);
v___x_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4768_);
return v___x_4769_;
}
case 10:
{
lean_object* v_expr_4770_; 
v_expr_4770_ = lean_ctor_get(v_x_4707_, 1);
lean_inc_ref(v_expr_4770_);
lean_dec_ref_known(v_x_4707_, 2);
v_x_4707_ = v_expr_4770_;
goto _start;
}
default: 
{
uint8_t v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
lean_dec_ref(v_x_4707_);
v___x_4772_ = 2;
v___x_4773_ = lean_box(v___x_4772_);
v___x_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
return v___x_4774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Lean_Meta_isTypeQuick(v_x_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___x_4788_; 
lean_inc_ref(v_e_4782_);
v___x_4788_ = l_Lean_Meta_isTypeQuick(v_e_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4838_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4838_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4838_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
uint8_t v___x_4793_; 
v___x_4793_ = lean_unbox(v_a_4789_);
lean_dec(v_a_4789_);
switch(v___x_4793_)
{
case 0:
{
uint8_t v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4797_; 
lean_dec_ref(v_e_4782_);
v___x_4794_ = 0;
v___x_4795_ = lean_box(v___x_4794_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4795_);
v___x_4797_ = v___x_4791_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
case 1:
{
uint8_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; 
lean_dec_ref(v_e_4782_);
v___x_4799_ = 1;
v___x_4800_ = lean_box(v___x_4799_);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4800_);
v___x_4802_ = v___x_4791_;
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
default: 
{
lean_object* v___x_4804_; 
lean_del_object(v___x_4791_);
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
lean_inc(v_a_4784_);
lean_inc_ref(v_a_4783_);
v___x_4804_ = lean_infer_type(v_e_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4806_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4804_, 1);
v___x_4806_ = l_Lean_Meta_whnfD(v_a_4805_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4821_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4821_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4821_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
if (lean_obj_tag(v_a_4807_) == 3)
{
uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4814_; 
lean_dec_ref_known(v_a_4807_, 1);
v___x_4811_ = 1;
v___x_4812_ = lean_box(v___x_4811_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4812_);
v___x_4814_ = v___x_4809_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
else
{
uint8_t v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4819_; 
lean_dec(v_a_4807_);
v___x_4816_ = 0;
v___x_4817_ = lean_box(v___x_4816_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4817_);
v___x_4819_ = v___x_4809_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4817_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
v_a_4822_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4806_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4806_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
v_a_4830_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4804_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4804_);
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
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec_ref(v_e_4782_);
v_a_4839_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4788_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4788_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Lean_Meta_isType(v_e_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4854_){
_start:
{
switch(lean_obj_tag(v_x_4854_))
{
case 7:
{
lean_object* v_body_4855_; 
v_body_4855_ = lean_ctor_get(v_x_4854_, 2);
v_x_4854_ = v_body_4855_;
goto _start;
}
case 3:
{
lean_object* v_u_4857_; lean_object* v___x_4858_; 
v_u_4857_ = lean_ctor_get(v_x_4854_, 0);
lean_inc(v_u_4857_);
v___x_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4858_, 0, v_u_4857_);
return v___x_4858_;
}
default: 
{
lean_object* v___x_4859_; 
v___x_4859_ = lean_box(0);
return v___x_4859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4860_);
lean_dec_ref(v_x_4860_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4862_, lean_object* v_body_4863_, lean_object* v_x_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4862_, v_body_4863_, v_x_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
lean_dec(v___y_4866_);
lean_dec_ref(v___y_4865_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4873_, lean_object* v_xs_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v_l_4881_; 
switch(lean_obj_tag(v_type_4873_))
{
case 3:
{
lean_object* v_u_4884_; 
lean_dec_ref(v_xs_4874_);
v_u_4884_ = lean_ctor_get(v_type_4873_, 0);
lean_inc(v_u_4884_);
lean_dec_ref_known(v_type_4873_, 1);
v_l_4881_ = v_u_4884_;
goto v___jp_4880_;
}
case 7:
{
lean_object* v_binderName_4885_; lean_object* v_binderType_4886_; lean_object* v_body_4887_; uint8_t v_binderInfo_4888_; lean_object* v___f_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
v_binderName_4885_ = lean_ctor_get(v_type_4873_, 0);
lean_inc(v_binderName_4885_);
v_binderType_4886_ = lean_ctor_get(v_type_4873_, 1);
lean_inc_ref(v_binderType_4886_);
v_body_4887_ = lean_ctor_get(v_type_4873_, 2);
lean_inc_ref(v_body_4887_);
v_binderInfo_4888_ = lean_ctor_get_uint8(v_type_4873_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4873_, 3);
lean_inc_ref(v_xs_4874_);
v___f_4889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4889_, 0, v_xs_4874_);
lean_closure_set(v___f_4889_, 1, v_body_4887_);
v___x_4890_ = lean_expr_instantiate_rev(v_binderType_4886_, v_xs_4874_);
lean_dec_ref(v_xs_4874_);
lean_dec_ref(v_binderType_4886_);
v___x_4891_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4885_, v_binderInfo_4888_, v___x_4890_, v___f_4889_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
return v___x_4891_;
}
default: 
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4892_ = lean_expr_instantiate_rev(v_type_4873_, v_xs_4874_);
lean_dec_ref(v_xs_4874_);
lean_dec_ref(v_type_4873_);
v___x_4893_ = l_Lean_Meta_whnfD(v___x_4892_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4905_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4896_ = v___x_4893_;
v_isShared_4897_ = v_isSharedCheck_4905_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4893_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4905_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
switch(lean_obj_tag(v_a_4894_))
{
case 3:
{
lean_object* v_u_4898_; 
lean_del_object(v___x_4896_);
v_u_4898_ = lean_ctor_get(v_a_4894_, 0);
lean_inc(v_u_4898_);
lean_dec_ref_known(v_a_4894_, 1);
v_l_4881_ = v_u_4898_;
goto v___jp_4880_;
}
case 7:
{
lean_object* v___x_4899_; 
lean_del_object(v___x_4896_);
v___x_4899_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4873_ = v_a_4894_;
v_xs_4874_ = v___x_4899_;
goto _start;
}
default: 
{
lean_object* v___x_4901_; lean_object* v___x_4903_; 
lean_dec(v_a_4894_);
v___x_4901_ = lean_box(0);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 0, v___x_4901_);
v___x_4903_ = v___x_4896_;
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
}
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
v_a_4906_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4893_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4893_);
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
v___jp_4880_:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4882_, 0, v_l_4881_);
v___x_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
return v___x_4883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4914_, lean_object* v_body_4915_, lean_object* v_x_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_){
_start:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4922_ = lean_array_push(v_xs_4914_, v_x_4916_);
v___x_4923_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4915_, v___x_4922_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4924_, lean_object* v_xs_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4924_, v_xs_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4932_, lean_object* v_cache_4933_, lean_object* v_a_x3f_4934_){
_start:
{
lean_object* v___x_4936_; lean_object* v_mctx_4937_; lean_object* v_zetaDeltaFVarIds_4938_; lean_object* v_postponed_4939_; lean_object* v_diag_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4950_; 
v___x_4936_ = lean_st_ref_take(v_a_4932_);
v_mctx_4937_ = lean_ctor_get(v___x_4936_, 0);
v_zetaDeltaFVarIds_4938_ = lean_ctor_get(v___x_4936_, 2);
v_postponed_4939_ = lean_ctor_get(v___x_4936_, 3);
v_diag_4940_ = lean_ctor_get(v___x_4936_, 4);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4950_ == 0)
{
lean_object* v_unused_4951_; 
v_unused_4951_ = lean_ctor_get(v___x_4936_, 1);
lean_dec(v_unused_4951_);
v___x_4942_ = v___x_4936_;
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_diag_4940_);
lean_inc(v_postponed_4939_);
lean_inc(v_zetaDeltaFVarIds_4938_);
lean_inc(v_mctx_4937_);
lean_dec(v___x_4936_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4944_; lean_object* v___x_4946_; 
v___x_4944_ = lean_box(0);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 1, v_cache_4933_);
v___x_4946_ = v___x_4942_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_mctx_4937_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_cache_4933_);
lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_zetaDeltaFVarIds_4938_);
lean_ctor_set(v_reuseFailAlloc_4949_, 3, v_postponed_4939_);
lean_ctor_set(v_reuseFailAlloc_4949_, 4, v_diag_4940_);
v___x_4946_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4947_ = lean_st_ref_put(v_a_4932_, v___x_4946_);
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4944_);
return v___x_4948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4952_, lean_object* v_cache_4953_, lean_object* v_a_x3f_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4952_, v_cache_4953_, v_a_x3f_4954_);
lean_dec(v_a_x3f_4954_);
lean_dec(v_a_4952_);
return v_res_4956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v___x_4963_; 
v___x_4963_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4957_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v_cache_4966_; lean_object* v___x_4967_; 
v___x_4964_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4965_ = lean_st_ref_get(v_a_4959_);
v_cache_4966_ = lean_ctor_get(v___x_4965_, 1);
lean_inc_ref(v_cache_4966_);
lean_dec(v___x_4965_);
v___x_4967_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4957_, v___x_4964_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4984_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4970_ = v___x_4967_;
v_isShared_4971_ = v_isSharedCheck_4984_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4967_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4984_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
lean_inc(v_a_4968_);
if (v_isShared_4971_ == 0)
{
lean_ctor_set_tag(v___x_4970_, 1);
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
lean_object* v___x_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4981_; 
v___x_4974_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4959_, v_cache_4966_, v___x_4973_);
lean_dec_ref(v___x_4973_);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4981_ == 0)
{
lean_object* v_unused_4982_; 
v_unused_4982_ = lean_ctor_get(v___x_4974_, 0);
lean_dec(v_unused_4982_);
v___x_4976_ = v___x_4974_;
v_isShared_4977_ = v_isSharedCheck_4981_;
goto v_resetjp_4975_;
}
else
{
lean_dec(v___x_4974_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4981_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4979_; 
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v_a_4968_);
v___x_4979_ = v___x_4976_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_a_4968_);
v___x_4979_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
return v___x_4979_;
}
}
}
}
}
else
{
lean_object* v_a_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
v_a_4985_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4985_);
lean_dec_ref_known(v___x_4967_, 1);
v___x_4986_ = lean_box(0);
v___x_4987_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4959_, v_cache_4966_, v___x_4986_);
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
lean_ctor_set_tag(v___x_4989_, 1);
lean_ctor_set(v___x_4989_, 0, v_a_4985_);
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4985_);
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
else
{
lean_object* v___x_4996_; 
lean_dec_ref(v_type_4957_);
v___x_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4963_);
return v___x_4996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v_res_5003_; 
v_res_5003_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
lean_dec(v_a_5001_);
lean_dec_ref(v_a_5000_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_){
_start:
{
lean_object* v___x_5010_; 
v___x_5010_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v_a_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5025_; 
v_a_5011_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5013_ = v___x_5010_;
v_isShared_5014_ = v_isSharedCheck_5025_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_a_5011_);
lean_dec(v___x_5010_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5025_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
if (lean_obj_tag(v_a_5011_) == 0)
{
uint8_t v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5018_; 
v___x_5015_ = 0;
v___x_5016_ = lean_box(v___x_5015_);
if (v_isShared_5014_ == 0)
{
lean_ctor_set(v___x_5013_, 0, v___x_5016_);
v___x_5018_ = v___x_5013_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_5016_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
else
{
uint8_t v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5023_; 
lean_dec_ref_known(v_a_5011_, 1);
v___x_5020_ = 1;
v___x_5021_ = lean_box(v___x_5020_);
if (v_isShared_5014_ == 0)
{
lean_ctor_set(v___x_5013_, 0, v___x_5021_);
v___x_5023_ = v___x_5013_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5021_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
v_a_5026_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_5010_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5010_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l_Lean_Meta_isTypeFormerType(v_type_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
return v_res_5040_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5041_, lean_object* v_x_5042_){
_start:
{
if (lean_obj_tag(v_x_5041_) == 0)
{
if (lean_obj_tag(v_x_5042_) == 0)
{
uint8_t v___x_5043_; 
v___x_5043_ = 1;
return v___x_5043_;
}
else
{
uint8_t v___x_5044_; 
v___x_5044_ = 0;
return v___x_5044_;
}
}
else
{
if (lean_obj_tag(v_x_5042_) == 0)
{
uint8_t v___x_5045_; 
v___x_5045_ = 0;
return v___x_5045_;
}
else
{
lean_object* v_val_5046_; lean_object* v_val_5047_; uint8_t v___x_5048_; 
v_val_5046_ = lean_ctor_get(v_x_5041_, 0);
v_val_5047_ = lean_ctor_get(v_x_5042_, 0);
v___x_5048_ = lean_level_eq(v_val_5046_, v_val_5047_);
return v___x_5048_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5049_, lean_object* v_x_5050_){
_start:
{
uint8_t v_res_5051_; lean_object* v_r_5052_; 
v_res_5051_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5049_, v_x_5050_);
lean_dec(v_x_5050_);
lean_dec(v_x_5049_);
v_r_5052_ = lean_box(v_res_5051_);
return v_r_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5072_; 
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5064_ = v___x_5061_;
v_isShared_5065_ = v_isSharedCheck_5072_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5061_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5072_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; uint8_t v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5066_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5067_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5062_, v___x_5066_);
lean_dec(v_a_5062_);
v___x_5068_ = lean_box(v___x_5067_);
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 0, v___x_5068_);
v___x_5070_ = v___x_5064_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
v_a_5073_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5061_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5061_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_Meta_isPropFormerType(v_type_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_);
lean_dec(v_a_5085_);
lean_dec_ref(v_a_5084_);
lean_dec(v_a_5083_);
lean_dec_ref(v_a_5082_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v___x_5094_; 
lean_inc(v_a_5092_);
lean_inc_ref(v_a_5091_);
lean_inc(v_a_5090_);
lean_inc_ref(v_a_5089_);
v___x_5094_ = lean_infer_type(v_e_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v___x_5096_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref_known(v___x_5094_, 1);
v___x_5096_ = l_Lean_Meta_isTypeFormerType(v_a_5095_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
return v___x_5096_;
}
else
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
v_a_5097_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5094_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5094_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Meta_isTypeFormer(v_e_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
lean_dec(v_a_5107_);
lean_dec_ref(v_a_5106_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5112_, lean_object* v_maxFVars_x3f_5113_, lean_object* v_k_5114_, uint8_t v_cleanupAnnotations_5115_, uint8_t v_whnfType_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v___f_5122_; lean_object* v___x_5123_; 
v___f_5122_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5122_, 0, v_k_5114_);
v___x_5123_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5112_, v_maxFVars_x3f_5113_, v___f_5122_, v_cleanupAnnotations_5115_, v_whnfType_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5123_) == 0)
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_5123_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5123_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5129_; 
if (v_isShared_5127_ == 0)
{
v___x_5129_ = v___x_5126_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5124_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
else
{
lean_object* v_a_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
v_a_5132_ = lean_ctor_get(v___x_5123_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5123_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_a_5132_);
lean_dec(v___x_5123_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5140_, lean_object* v_maxFVars_x3f_5141_, lean_object* v_k_5142_, lean_object* v_cleanupAnnotations_5143_, lean_object* v_whnfType_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5150_; uint8_t v_whnfType_boxed_5151_; lean_object* v_res_5152_; 
v_cleanupAnnotations_boxed_5150_ = lean_unbox(v_cleanupAnnotations_5143_);
v_whnfType_boxed_5151_ = lean_unbox(v_whnfType_5144_);
v_res_5152_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5140_, v_maxFVars_x3f_5141_, v_k_5142_, v_cleanupAnnotations_boxed_5150_, v_whnfType_boxed_5151_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5153_, lean_object* v_type_5154_, lean_object* v_maxFVars_x3f_5155_, lean_object* v_k_5156_, uint8_t v_cleanupAnnotations_5157_, uint8_t v_whnfType_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
lean_object* v___x_5164_; 
v___x_5164_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5154_, v_maxFVars_x3f_5155_, v_k_5156_, v_cleanupAnnotations_5157_, v_whnfType_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5165_, lean_object* v_type_5166_, lean_object* v_maxFVars_x3f_5167_, lean_object* v_k_5168_, lean_object* v_cleanupAnnotations_5169_, lean_object* v_whnfType_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5176_; uint8_t v_whnfType_boxed_5177_; lean_object* v_res_5178_; 
v_cleanupAnnotations_boxed_5176_ = lean_unbox(v_cleanupAnnotations_5169_);
v_whnfType_boxed_5177_ = lean_unbox(v_whnfType_5170_);
v_res_5178_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5165_, v_type_5166_, v_maxFVars_x3f_5167_, v_k_5168_, v_cleanupAnnotations_boxed_5176_, v_whnfType_boxed_5177_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
return v_res_5178_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5179_, lean_object* v_as_5180_, size_t v_i_5181_, size_t v_stop_5182_){
_start:
{
uint8_t v___x_5183_; 
v___x_5183_ = lean_usize_dec_eq(v_i_5181_, v_stop_5182_);
if (v___x_5183_ == 0)
{
lean_object* v___x_5184_; uint8_t v___x_5185_; 
v___x_5184_ = lean_array_uget_borrowed(v_as_5180_, v_i_5181_);
v___x_5185_ = lean_expr_eqv(v_a_5179_, v___x_5184_);
if (v___x_5185_ == 0)
{
size_t v___x_5186_; size_t v___x_5187_; 
v___x_5186_ = ((size_t)1ULL);
v___x_5187_ = lean_usize_add(v_i_5181_, v___x_5186_);
v_i_5181_ = v___x_5187_;
goto _start;
}
else
{
return v___x_5185_;
}
}
else
{
uint8_t v___x_5189_; 
v___x_5189_ = 0;
return v___x_5189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5190_, lean_object* v_as_5191_, lean_object* v_i_5192_, lean_object* v_stop_5193_){
_start:
{
size_t v_i_boxed_5194_; size_t v_stop_boxed_5195_; uint8_t v_res_5196_; lean_object* v_r_5197_; 
v_i_boxed_5194_ = lean_unbox_usize(v_i_5192_);
lean_dec(v_i_5192_);
v_stop_boxed_5195_ = lean_unbox_usize(v_stop_5193_);
lean_dec(v_stop_5193_);
v_res_5196_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5190_, v_as_5191_, v_i_boxed_5194_, v_stop_boxed_5195_);
lean_dec_ref(v_as_5191_);
lean_dec_ref(v_a_5190_);
v_r_5197_ = lean_box(v_res_5196_);
return v_r_5197_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; uint8_t v___x_5202_; 
v___x_5200_ = lean_unsigned_to_nat(0u);
v___x_5201_ = lean_array_get_size(v_as_5198_);
v___x_5202_ = lean_nat_dec_lt(v___x_5200_, v___x_5201_);
if (v___x_5202_ == 0)
{
return v___x_5202_;
}
else
{
size_t v___x_5203_; size_t v___x_5204_; uint8_t v___x_5205_; 
v___x_5203_ = ((size_t)0ULL);
v___x_5204_ = lean_usize_of_nat(v___x_5201_);
v___x_5205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5199_, v_as_5198_, v___x_5203_, v___x_5204_);
return v___x_5205_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5206_, lean_object* v_a_5207_){
_start:
{
uint8_t v_res_5208_; lean_object* v_r_5209_; 
v_res_5208_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5206_, v_a_5207_);
lean_dec_ref(v_a_5207_);
lean_dec_ref(v_as_5206_);
v_r_5209_ = lean_box(v_res_5208_);
return v_r_5209_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5210_, lean_object* v_e_5211_){
_start:
{
uint8_t v___x_5212_; lean_object* v_d_5214_; lean_object* v_b_5215_; 
v___x_5212_ = l_Lean_Expr_hasFVar(v_e_5211_);
if (v___x_5212_ == 0)
{
lean_dec_ref(v_e_5211_);
return v___x_5212_;
}
else
{
switch(lean_obj_tag(v_e_5211_))
{
case 7:
{
lean_object* v_binderType_5218_; lean_object* v_body_5219_; 
v_binderType_5218_ = lean_ctor_get(v_e_5211_, 1);
lean_inc_ref(v_binderType_5218_);
v_body_5219_ = lean_ctor_get(v_e_5211_, 2);
lean_inc_ref(v_body_5219_);
lean_dec_ref_known(v_e_5211_, 3);
v_d_5214_ = v_binderType_5218_;
v_b_5215_ = v_body_5219_;
goto v___jp_5213_;
}
case 6:
{
lean_object* v_binderType_5220_; lean_object* v_body_5221_; 
v_binderType_5220_ = lean_ctor_get(v_e_5211_, 1);
lean_inc_ref(v_binderType_5220_);
v_body_5221_ = lean_ctor_get(v_e_5211_, 2);
lean_inc_ref(v_body_5221_);
lean_dec_ref_known(v_e_5211_, 3);
v_d_5214_ = v_binderType_5220_;
v_b_5215_ = v_body_5221_;
goto v___jp_5213_;
}
case 10:
{
lean_object* v_expr_5222_; 
v_expr_5222_ = lean_ctor_get(v_e_5211_, 1);
lean_inc_ref(v_expr_5222_);
lean_dec_ref_known(v_e_5211_, 2);
v_e_5211_ = v_expr_5222_;
goto _start;
}
case 8:
{
lean_object* v_type_5224_; lean_object* v_value_5225_; lean_object* v_body_5226_; uint8_t v___x_5227_; 
v_type_5224_ = lean_ctor_get(v_e_5211_, 1);
lean_inc_ref(v_type_5224_);
v_value_5225_ = lean_ctor_get(v_e_5211_, 2);
lean_inc_ref(v_value_5225_);
v_body_5226_ = lean_ctor_get(v_e_5211_, 3);
lean_inc_ref(v_body_5226_);
lean_dec_ref_known(v_e_5211_, 4);
v___x_5227_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5210_, v_type_5224_);
if (v___x_5227_ == 0)
{
uint8_t v___x_5228_; 
v___x_5228_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5210_, v_value_5225_);
if (v___x_5228_ == 0)
{
v_e_5211_ = v_body_5226_;
goto _start;
}
else
{
lean_dec_ref(v_body_5226_);
return v___x_5212_;
}
}
else
{
lean_dec_ref(v_body_5226_);
lean_dec_ref(v_value_5225_);
return v___x_5212_;
}
}
case 5:
{
lean_object* v_fn_5230_; lean_object* v_arg_5231_; uint8_t v___x_5232_; 
v_fn_5230_ = lean_ctor_get(v_e_5211_, 0);
lean_inc_ref(v_fn_5230_);
v_arg_5231_ = lean_ctor_get(v_e_5211_, 1);
lean_inc_ref(v_arg_5231_);
lean_dec_ref_known(v_e_5211_, 2);
v___x_5232_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5210_, v_fn_5230_);
if (v___x_5232_ == 0)
{
v_e_5211_ = v_arg_5231_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5231_);
return v___x_5212_;
}
}
case 11:
{
lean_object* v_struct_5234_; 
v_struct_5234_ = lean_ctor_get(v_e_5211_, 2);
lean_inc_ref(v_struct_5234_);
lean_dec_ref_known(v_e_5211_, 3);
v_e_5211_ = v_struct_5234_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5236_; lean_object* v___x_5237_; uint8_t v___x_5238_; 
v_fvarId_5236_ = lean_ctor_get(v_e_5211_, 0);
lean_inc(v_fvarId_5236_);
lean_dec_ref_known(v_e_5211_, 1);
v___x_5237_ = l_Lean_Expr_fvar___override(v_fvarId_5236_);
v___x_5238_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5210_, v___x_5237_);
lean_dec_ref(v___x_5237_);
return v___x_5238_;
}
default: 
{
uint8_t v___x_5239_; 
lean_dec_ref(v_e_5211_);
v___x_5239_ = 0;
return v___x_5239_;
}
}
}
v___jp_5213_:
{
uint8_t v___x_5216_; 
v___x_5216_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5210_, v_d_5214_);
if (v___x_5216_ == 0)
{
v_e_5211_ = v_b_5215_;
goto _start;
}
else
{
lean_dec_ref(v_b_5215_);
return v___x_5212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5240_, lean_object* v_e_5241_){
_start:
{
uint8_t v_res_5242_; lean_object* v_r_5243_; 
v_res_5242_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5240_, v_e_5241_);
lean_dec_ref(v_xs_5240_);
v_r_5243_ = lean_box(v_res_5242_);
return v_r_5243_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5246_ = l_Lean_stringToMessageData(v___x_5245_);
return v___x_5246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5249_ = l_Lean_stringToMessageData(v___x_5248_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5250_, lean_object* v_type_5251_, lean_object* v_as_5252_, size_t v_sz_5253_, size_t v_i_5254_, lean_object* v_b_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_a_5262_; uint8_t v___x_5266_; 
v___x_5266_ = lean_usize_dec_lt(v_i_5254_, v_sz_5253_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; 
lean_dec_ref(v_type_5251_);
v___x_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5267_, 0, v_b_5255_);
return v___x_5267_;
}
else
{
lean_object* v___x_5268_; lean_object* v_a_5269_; uint8_t v___x_5270_; 
v___x_5268_ = lean_box(0);
v_a_5269_ = lean_array_uget_borrowed(v_as_5252_, v_i_5254_);
lean_inc(v_a_5269_);
v___x_5270_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5250_, v_a_5269_);
if (v___x_5270_ == 0)
{
v_a_5262_ = v___x_5268_;
goto v___jp_5261_;
}
else
{
lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5271_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5269_);
v___x_5272_ = l_Lean_MessageData_ofExpr(v_a_5269_);
v___x_5273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5271_);
lean_ctor_set(v___x_5273_, 1, v___x_5272_);
v___x_5274_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5273_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
lean_inc_ref(v_type_5251_);
v___x_5276_ = l_Lean_MessageData_ofExpr(v_type_5251_);
v___x_5277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5275_);
lean_ctor_set(v___x_5277_, 1, v___x_5276_);
v___x_5278_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5277_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
if (lean_obj_tag(v___x_5278_) == 0)
{
lean_dec_ref_known(v___x_5278_, 1);
v_a_5262_ = v___x_5268_;
goto v___jp_5261_;
}
else
{
lean_dec_ref(v_type_5251_);
return v___x_5278_;
}
}
}
v___jp_5261_:
{
size_t v___x_5263_; size_t v___x_5264_; 
v___x_5263_ = ((size_t)1ULL);
v___x_5264_ = lean_usize_add(v_i_5254_, v___x_5263_);
v_i_5254_ = v___x_5264_;
v_b_5255_ = v_a_5262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5279_, lean_object* v_type_5280_, lean_object* v_as_5281_, lean_object* v_sz_5282_, lean_object* v_i_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
size_t v_sz_boxed_5290_; size_t v_i_boxed_5291_; lean_object* v_res_5292_; 
v_sz_boxed_5290_ = lean_unbox_usize(v_sz_5282_);
lean_dec(v_sz_5282_);
v_i_boxed_5291_ = lean_unbox_usize(v_i_5283_);
lean_dec(v_i_5283_);
v_res_5292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5279_, v_type_5280_, v_as_5281_, v_sz_boxed_5290_, v_i_boxed_5291_, v_b_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec_ref(v_as_5281_);
lean_dec_ref(v_xs_5279_);
return v_res_5292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5293_, size_t v_i_5294_, lean_object* v_bs_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
uint8_t v___x_5301_; 
v___x_5301_ = lean_usize_dec_lt(v_i_5294_, v_sz_5293_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; 
v___x_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5302_, 0, v_bs_5295_);
return v___x_5302_;
}
else
{
lean_object* v_v_5303_; lean_object* v___x_5304_; lean_object* v_bs_x27_5305_; lean_object* v___x_5306_; 
v_v_5303_ = lean_array_uget(v_bs_5295_, v_i_5294_);
v___x_5304_ = lean_unsigned_to_nat(0u);
v_bs_x27_5305_ = lean_array_uset(v_bs_5295_, v_i_5294_, v___x_5304_);
lean_inc(v___y_5299_);
lean_inc_ref(v___y_5298_);
lean_inc(v___y_5297_);
lean_inc_ref(v___y_5296_);
v___x_5306_ = lean_infer_type(v_v_5303_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; size_t v___x_5308_; size_t v___x_5309_; lean_object* v___x_5310_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
lean_dec_ref_known(v___x_5306_, 1);
v___x_5308_ = ((size_t)1ULL);
v___x_5309_ = lean_usize_add(v_i_5294_, v___x_5308_);
v___x_5310_ = lean_array_uset(v_bs_x27_5305_, v_i_5294_, v_a_5307_);
v_i_5294_ = v___x_5309_;
v_bs_5295_ = v___x_5310_;
goto _start;
}
else
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
lean_dec_ref(v_bs_x27_5305_);
v_a_5312_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5306_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5306_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5320_, lean_object* v_i_5321_, lean_object* v_bs_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
size_t v_sz_boxed_5328_; size_t v_i_boxed_5329_; lean_object* v_res_5330_; 
v_sz_boxed_5328_ = lean_unbox_usize(v_sz_5320_);
lean_dec(v_sz_5320_);
v_i_boxed_5329_ = lean_unbox_usize(v_i_5321_);
lean_dec(v_i_5321_);
v_res_5330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5328_, v_i_boxed_5329_, v_bs_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
return v_res_5330_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
v___x_5332_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5333_ = l_Lean_stringToMessageData(v___x_5332_);
return v___x_5333_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5335_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5336_ = l_Lean_stringToMessageData(v___x_5335_);
return v___x_5336_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5338_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5339_ = l_Lean_stringToMessageData(v___x_5338_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5340_, lean_object* v_n_5341_, lean_object* v_xs_5342_, lean_object* v_x_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v___x_5373_; uint8_t v___x_5374_; 
v___x_5373_ = lean_array_get_size(v_xs_5342_);
v___x_5374_ = lean_nat_dec_eq(v___x_5373_, v_n_5341_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
lean_dec_ref(v_xs_5342_);
v___x_5375_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5376_ = l_Lean_MessageData_ofExpr(v_type_5340_);
v___x_5377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5377_, 0, v___x_5375_);
lean_ctor_set(v___x_5377_, 1, v___x_5376_);
v___x_5378_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5379_, 0, v___x_5377_);
lean_ctor_set(v___x_5379_, 1, v___x_5378_);
v___x_5380_ = l_Nat_reprFast(v_n_5341_);
v___x_5381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5380_);
v___x_5382_ = l_Lean_MessageData_ofFormat(v___x_5381_);
v___x_5383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5379_);
lean_ctor_set(v___x_5383_, 1, v___x_5382_);
v___x_5384_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5383_);
lean_ctor_set(v___x_5385_, 1, v___x_5384_);
v___x_5386_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5385_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_);
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5386_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5386_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5392_; 
if (v_isShared_5390_ == 0)
{
v___x_5392_ = v___x_5389_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
else
{
lean_dec(v_n_5341_);
goto v___jp_5349_;
}
v___jp_5349_:
{
size_t v_sz_5350_; size_t v___x_5351_; lean_object* v___x_5352_; 
v_sz_5350_ = lean_array_size(v_xs_5342_);
v___x_5351_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5342_);
v___x_5352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5350_, v___x_5351_, v_xs_5342_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5354_; size_t v_sz_5355_; lean_object* v___x_5356_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
lean_inc(v_a_5353_);
lean_dec_ref_known(v___x_5352_, 1);
v___x_5354_ = lean_box(0);
v_sz_5355_ = lean_array_size(v_a_5353_);
v___x_5356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5342_, v_type_5340_, v_a_5353_, v_sz_5355_, v___x_5351_, v___x_5354_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_);
lean_dec_ref(v_xs_5342_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5363_ == 0)
{
lean_object* v_unused_5364_; 
v_unused_5364_ = lean_ctor_get(v___x_5356_, 0);
lean_dec(v_unused_5364_);
v___x_5358_ = v___x_5356_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_dec(v___x_5356_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v_a_5353_);
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5353_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec(v_a_5353_);
v_a_5365_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5356_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5356_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5342_);
lean_dec_ref(v_type_5340_);
return v___x_5352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5395_, lean_object* v_n_5396_, lean_object* v_xs_5397_, lean_object* v_x_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5395_, v_n_5396_, v_xs_5397_, v_x_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
lean_dec(v___y_5400_);
lean_dec_ref(v___y_5399_);
lean_dec_ref(v_x_5398_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5405_, lean_object* v_type_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v___f_5412_; lean_object* v___x_5413_; uint8_t v___x_5414_; lean_object* v___x_5415_; 
lean_inc(v_n_5405_);
lean_inc_ref(v_type_5406_);
v___f_5412_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5412_, 0, v_type_5406_);
lean_closure_set(v___f_5412_, 1, v_n_5405_);
v___x_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5413_, 0, v_n_5405_);
v___x_5414_ = 0;
v___x_5415_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5406_, v___x_5413_, v___f_5412_, v___x_5414_, v___x_5414_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5416_, lean_object* v_type_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l_Lean_Meta_arrowDomainsN(v_n_5416_, v_type_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_);
lean_dec(v_a_5421_);
lean_dec_ref(v_a_5420_);
lean_dec(v_a_5419_);
lean_dec_ref(v_a_5418_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5424_, lean_object* v_e_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_){
_start:
{
lean_object* v___x_5431_; 
lean_inc(v_a_5429_);
lean_inc_ref(v_a_5428_);
lean_inc(v_a_5427_);
lean_inc_ref(v_a_5426_);
v___x_5431_ = lean_infer_type(v_e_5425_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v_a_5432_; lean_object* v___x_5433_; 
v_a_5432_ = lean_ctor_get(v___x_5431_, 0);
lean_inc(v_a_5432_);
lean_dec_ref_known(v___x_5431_, 1);
v___x_5433_ = l_Lean_Meta_arrowDomainsN(v_n_5424_, v_a_5432_, v_a_5426_, v_a_5427_, v_a_5428_, v_a_5429_);
return v___x_5433_;
}
else
{
lean_object* v_a_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5441_; 
lean_dec(v_n_5424_);
v_a_5434_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5441_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5441_ == 0)
{
v___x_5436_ = v___x_5431_;
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_a_5434_);
lean_dec(v___x_5431_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5441_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5439_; 
if (v_isShared_5437_ == 0)
{
v___x_5439_ = v___x_5436_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_a_5434_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5442_, lean_object* v_e_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_){
_start:
{
lean_object* v_res_5449_; 
v_res_5449_ = l_Lean_Meta_inferArgumentTypesN(v_n_5442_, v_e_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_);
lean_dec(v_a_5447_);
lean_dec_ref(v_a_5446_);
lean_dec(v_a_5445_);
lean_dec_ref(v_a_5444_);
return v_res_5449_;
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
