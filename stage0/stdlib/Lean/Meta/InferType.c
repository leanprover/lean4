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
lean_object* v_toCold_959_; lean_object* v_currRecDepth_960_; lean_object* v_ref_961_; uint16_t v_optionFlags_962_; uint8_t v_suppressElabErrors_963_; uint8_t v_isRecordingDeps_964_; lean_object* v_ref_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_toCold_959_ = lean_ctor_get(v___y_956_, 0);
v_currRecDepth_960_ = lean_ctor_get(v___y_956_, 1);
v_ref_961_ = lean_ctor_get(v___y_956_, 2);
v_optionFlags_962_ = lean_ctor_get_uint16(v___y_956_, sizeof(void*)*3);
v_suppressElabErrors_963_ = lean_ctor_get_uint8(v___y_956_, sizeof(void*)*3 + 2);
v_isRecordingDeps_964_ = lean_ctor_get_uint8(v___y_956_, sizeof(void*)*3 + 3);
v_ref_965_ = l_Lean_replaceRef(v_ref_952_, v_ref_961_);
lean_inc(v_currRecDepth_960_);
lean_inc_ref(v_toCold_959_);
v___x_966_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_966_, 0, v_toCold_959_);
lean_ctor_set(v___x_966_, 1, v_currRecDepth_960_);
lean_ctor_set(v___x_966_, 2, v_ref_965_);
lean_ctor_set_uint16(v___x_966_, sizeof(void*)*3, v_optionFlags_962_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*3 + 2, v_suppressElabErrors_963_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*3 + 3, v_isRecordingDeps_964_);
v___x_967_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_953_, v___y_954_, v___y_955_, v___x_966_, v___y_957_);
lean_dec_ref_known(v___x_966_, 3);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_968_, lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_968_, v_msg_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v_ref_968_);
return v_res_975_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_979_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_982_, 11, v___x_979_);
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
v___x_1036_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1023_, v_declHint_1018_);
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
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1325_, lean_object* v_idx_1326_, lean_object* v_e_1327_, lean_object* v_a_1328_, lean_object* v_00_u03b1_1329_, lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1336_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1337_ = l_Lean_mkProj(v_structName_1325_, v_idx_1326_, v_e_1327_);
v___x_1338_ = l_Lean_indentExpr(v___x_1337_);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1336_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = l_Lean_indentExpr(v_a_1328_);
v___x_1343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1343_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1345_, lean_object* v_idx_1346_, lean_object* v_e_1347_, lean_object* v_a_1348_, lean_object* v_00_u03b1_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1345_, v_idx_1346_, v_e_1347_, v_a_1348_, v_00_u03b1_1349_, v_x_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v_env_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; 
v___x_1363_ = lean_st_ref_get(v___y_1361_);
v_env_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc_ref(v_env_1364_);
lean_dec(v___x_1363_);
v___x_1365_ = 0;
lean_inc(v_constName_1357_);
v___x_1366_ = l_Lean_Environment_find_x3f(v_env_1364_, v_constName_1357_, v___x_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_constName_1357_);
v_val_1368_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1366_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_val_1368_);
lean_dec(v___x_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 0);
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_val_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1383_, lean_object* v_structName_1384_, lean_object* v_e_1385_, lean_object* v_idx_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_a_1396_; uint8_t v___x_1400_; 
v___x_1400_ = lean_nat_dec_lt(v_a_1388_, v_upperBound_1383_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_idx_1386_);
lean_dec_ref(v_e_1385_);
lean_dec(v_structName_1384_);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_b_1389_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; 
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
v___x_1402_ = lean_whnf(v_b_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
if (lean_obj_tag(v_a_1403_) == 7)
{
lean_object* v_body_1404_; uint8_t v___x_1405_; 
v_body_1404_ = lean_ctor_get(v_a_1403_, 2);
lean_inc_ref(v_body_1404_);
lean_dec_ref_known(v_a_1403_, 3);
v___x_1405_ = l_Lean_Expr_hasLooseBVars(v_body_1404_);
if (v___x_1405_ == 0)
{
v_a_1396_ = v_body_1404_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_inc_ref(v_e_1385_);
lean_inc(v_a_1388_);
lean_inc(v_structName_1384_);
v___x_1406_ = l_Lean_mkProj(v_structName_1384_, v_a_1388_, v_e_1385_);
v___x_1407_ = lean_expr_instantiate1(v_body_1404_, v___x_1406_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v_body_1404_);
v_a_1396_ = v___x_1407_;
goto v___jp_1395_;
}
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1408_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1385_);
lean_inc(v_idx_1386_);
lean_inc(v_structName_1384_);
v___x_1409_ = l_Lean_mkProj(v_structName_1384_, v_idx_1386_, v_e_1385_);
v___x_1410_ = l_Lean_indentExpr(v___x_1409_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1408_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
lean_inc_ref(v_a_1387_);
v___x_1414_ = l_Lean_indentExpr(v_a_1387_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1415_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec_ref_known(v___x_1416_, 1);
v_a_1396_ = v_a_1403_;
goto v___jp_1395_;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_a_1403_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_idx_1386_);
lean_dec_ref(v_e_1385_);
lean_dec(v_structName_1384_);
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
else
{
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_idx_1386_);
lean_dec_ref(v_e_1385_);
lean_dec(v_structName_1384_);
return v___x_1402_;
}
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_add(v_a_1388_, v___x_1397_);
lean_dec(v_a_1388_);
v_a_1388_ = v___x_1398_;
v_b_1389_ = v_a_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1425_, lean_object* v_structName_1426_, lean_object* v_e_1427_, lean_object* v_idx_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1425_, v_structName_1426_, v_e_1427_, v_idx_1428_, v_a_1429_, v_a_1430_, v_b_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v_upperBound_1425_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1438_, lean_object* v_structName_1439_, lean_object* v_e_1440_, lean_object* v_idx_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_a_1451_; uint8_t v___x_1455_; 
v___x_1455_ = lean_nat_dec_lt(v_a_1443_, v_upperBound_1438_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_idx_1441_);
lean_dec_ref(v_e_1440_);
lean_dec(v_structName_1439_);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_b_1444_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; 
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
v___x_1457_ = lean_whnf(v_b_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
if (lean_obj_tag(v_a_1458_) == 7)
{
lean_object* v_body_1459_; uint8_t v___x_1460_; 
v_body_1459_ = lean_ctor_get(v_a_1458_, 2);
lean_inc_ref(v_body_1459_);
lean_dec_ref_known(v_a_1458_, 3);
v___x_1460_ = l_Lean_Expr_hasLooseBVars(v_body_1459_);
if (v___x_1460_ == 0)
{
v_a_1451_ = v_body_1459_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_inc_ref(v_e_1440_);
lean_inc(v_a_1443_);
lean_inc(v_structName_1439_);
v___x_1461_ = l_Lean_mkProj(v_structName_1439_, v_a_1443_, v_e_1440_);
v___x_1462_ = lean_expr_instantiate1(v_body_1459_, v___x_1461_);
lean_dec_ref(v___x_1461_);
lean_dec_ref(v_body_1459_);
v_a_1451_ = v___x_1462_;
goto v___jp_1450_;
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1463_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1440_);
lean_inc(v_idx_1441_);
lean_inc(v_structName_1439_);
v___x_1464_ = l_Lean_mkProj(v_structName_1439_, v_idx_1441_, v_e_1440_);
v___x_1465_ = l_Lean_indentExpr(v___x_1464_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1463_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
lean_inc_ref(v_a_1442_);
v___x_1469_ = l_Lean_indentExpr(v_a_1442_);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1470_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_dec_ref_known(v___x_1471_, 1);
v_a_1451_ = v_a_1458_;
goto v___jp_1450_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1458_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_idx_1441_);
lean_dec_ref(v_e_1440_);
lean_dec(v_structName_1439_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
else
{
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_idx_1441_);
lean_dec_ref(v_e_1440_);
lean_dec(v_structName_1439_);
return v___x_1457_;
}
}
v___jp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_a_1443_, v___x_1452_);
lean_dec(v_a_1443_);
v___x_1454_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1438_, v_structName_1439_, v_e_1440_, v_idx_1441_, v_a_1442_, v___x_1453_, v_a_1451_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1480_, lean_object* v_structName_1481_, lean_object* v_e_1482_, lean_object* v_idx_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1480_, v_structName_1481_, v_e_1482_, v_idx_1483_, v_a_1484_, v_a_1485_, v_b_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v_upperBound_1480_);
return v_res_1492_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1493_; lean_object* v_dummy_1494_; 
v___x_1493_ = lean_box(0);
v_dummy_1494_ = l_Lean_Expr_sort___override(v___x_1493_);
return v_dummy_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1495_, lean_object* v_idx_1496_, lean_object* v_e_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v___x_1503_; 
lean_inc(v_a_1501_);
lean_inc_ref(v_a_1500_);
lean_inc(v_a_1499_);
lean_inc_ref(v_a_1498_);
lean_inc_ref(v_e_1497_);
v___x_1503_ = lean_infer_type(v_e_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
lean_inc(v_a_1501_);
lean_inc_ref(v_a_1500_);
lean_inc(v_a_1499_);
lean_inc_ref(v_a_1498_);
v___x_1505_ = lean_whnf(v_a_1504_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = l_Lean_Expr_getAppFn(v_a_1506_);
if (lean_obj_tag(v___x_1507_) == 4)
{
lean_object* v_declName_1508_; lean_object* v_us_1509_; lean_object* v___x_1510_; lean_object* v_env_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
v_declName_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_declName_1508_);
v_us_1509_ = lean_ctor_get(v___x_1507_, 1);
lean_inc(v_us_1509_);
lean_dec_ref_known(v___x_1507_, 2);
v___x_1510_ = lean_st_ref_get(v_a_1501_);
v_env_1514_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_ref(v_env_1514_);
lean_dec(v___x_1510_);
v___x_1515_ = 0;
v___x_1516_ = l_Lean_Environment_find_x3f(v_env_1514_, v_declName_1508_, v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v_us_1509_);
v___x_1517_ = lean_box(0);
v___x_1518_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1517_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1518_;
}
else
{
lean_object* v_val_1519_; 
v_val_1519_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v___x_1516_, 1);
if (lean_obj_tag(v_val_1519_) == 5)
{
lean_object* v_val_1520_; lean_object* v_ctors_1521_; 
v_val_1520_ = lean_ctor_get(v_val_1519_, 0);
lean_inc_ref(v_val_1520_);
lean_dec_ref_known(v_val_1519_, 1);
v_ctors_1521_ = lean_ctor_get(v_val_1520_, 4);
lean_inc(v_ctors_1521_);
if (lean_obj_tag(v_ctors_1521_) == 1)
{
lean_object* v_tail_1522_; 
v_tail_1522_ = lean_ctor_get(v_ctors_1521_, 1);
if (lean_obj_tag(v_tail_1522_) == 0)
{
lean_object* v_toConstantVal_1523_; lean_object* v_numParams_1524_; lean_object* v_numIndices_1525_; lean_object* v_head_1526_; lean_object* v___x_1527_; 
v_toConstantVal_1523_ = lean_ctor_get(v_val_1520_, 0);
lean_inc_ref(v_toConstantVal_1523_);
v_numParams_1524_ = lean_ctor_get(v_val_1520_, 1);
lean_inc(v_numParams_1524_);
v_numIndices_1525_ = lean_ctor_get(v_val_1520_, 2);
lean_inc(v_numIndices_1525_);
lean_dec_ref(v_val_1520_);
v_head_1526_ = lean_ctor_get(v_ctors_1521_, 0);
lean_inc(v_head_1526_);
lean_dec_ref_known(v_ctors_1521_, 2);
v___x_1527_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1526_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
if (lean_obj_tag(v_a_1528_) == 6)
{
lean_object* v_val_1529_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v_name_1569_; uint8_t v___x_1570_; 
v_val_1529_ = lean_ctor_get(v_a_1528_, 0);
lean_inc_ref(v_val_1529_);
lean_dec_ref_known(v_a_1528_, 1);
v_name_1569_ = lean_ctor_get(v_toConstantVal_1523_, 0);
lean_inc(v_name_1569_);
lean_dec_ref(v_toConstantVal_1523_);
v___x_1570_ = lean_name_eq(v_name_1569_, v_structName_1495_);
lean_dec(v_name_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_val_1529_);
lean_dec(v_numIndices_1525_);
lean_dec(v_numParams_1524_);
lean_dec(v_us_1509_);
v___x_1571_ = lean_box(0);
v___x_1572_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1571_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
v___y_1531_ = v_a_1498_;
v___y_1532_ = v_a_1499_;
v___y_1533_ = v_a_1500_;
v___y_1534_ = v_a_1501_;
goto v___jp_1530_;
}
v___jp_1530_:
{
lean_object* v_dummy_1535_; lean_object* v_nargs_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_dummy_1535_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1536_ = l_Lean_Expr_getAppNumArgs(v_a_1506_);
lean_inc(v_nargs_1536_);
v___x_1537_ = lean_mk_array(v_nargs_1536_, v_dummy_1535_);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_sub(v_nargs_1536_, v___x_1538_);
lean_dec(v_nargs_1536_);
lean_inc(v_a_1506_);
v___x_1540_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1506_, v___x_1537_, v___x_1539_);
v___x_1541_ = lean_nat_add(v_numParams_1524_, v_numIndices_1525_);
lean_dec(v_numIndices_1525_);
v___x_1542_ = lean_array_get_size(v___x_1540_);
v___x_1543_ = lean_nat_dec_eq(v___x_1541_, v___x_1542_);
lean_dec(v___x_1541_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref(v___x_1540_);
lean_dec_ref(v_val_1529_);
lean_dec(v_numParams_1524_);
lean_dec(v_us_1509_);
v___x_1544_ = lean_box(0);
v___x_1545_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1544_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1545_;
}
else
{
lean_object* v_toConstantVal_1546_; lean_object* v_name_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_toConstantVal_1546_ = lean_ctor_get(v_val_1529_, 0);
lean_inc_ref(v_toConstantVal_1546_);
lean_dec_ref(v_val_1529_);
v_name_1547_ = lean_ctor_get(v_toConstantVal_1546_, 0);
lean_inc(v_name_1547_);
lean_dec_ref(v_toConstantVal_1546_);
v___x_1548_ = l_Lean_mkConst(v_name_1547_, v_us_1509_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = l_Array_toSubarray___redArg(v___x_1540_, v___x_1549_, v_numParams_1524_);
v___x_1551_ = l_Subarray_copy___redArg(v___x_1550_);
v___x_1552_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1548_, v___x_1551_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec_ref(v___x_1551_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
lean_inc(v_a_1506_);
lean_inc_ref(v_e_1497_);
lean_inc(v_structName_1495_);
lean_inc(v_idx_1496_);
v___x_1554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1496_, v_structName_1495_, v_e_1497_, v_idx_1496_, v_a_1506_, v___x_1549_, v_a_1553_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
lean_inc(v___y_1534_);
lean_inc_ref(v___y_1533_);
lean_inc(v___y_1532_);
lean_inc_ref(v___y_1531_);
v___x_1556_ = lean_whnf(v_a_1555_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1568_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1568_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1568_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
if (lean_obj_tag(v_a_1557_) == 7)
{
lean_object* v_binderType_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
lean_dec(v_a_1506_);
lean_dec_ref(v_e_1497_);
lean_dec(v_idx_1496_);
lean_dec(v_structName_1495_);
v_binderType_1561_ = lean_ctor_get(v_a_1557_, 1);
lean_inc_ref(v_binderType_1561_);
lean_dec_ref_known(v_a_1557_, 3);
v___x_1562_ = lean_expr_consume_type_annotations(v_binderType_1561_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1562_);
v___x_1564_ = v___x_1559_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_del_object(v___x_1559_);
lean_dec(v_a_1557_);
v___x_1566_ = lean_box(0);
v___x_1567_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1566_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1567_;
}
}
}
else
{
lean_dec(v_a_1506_);
lean_dec_ref(v_e_1497_);
lean_dec(v_idx_1496_);
lean_dec(v_structName_1495_);
return v___x_1556_;
}
}
else
{
lean_dec(v_a_1506_);
lean_dec_ref(v_e_1497_);
lean_dec(v_idx_1496_);
lean_dec(v_structName_1495_);
return v___x_1554_;
}
}
else
{
lean_dec(v_a_1506_);
lean_dec_ref(v_e_1497_);
lean_dec(v_idx_1496_);
lean_dec(v_structName_1495_);
return v___x_1552_;
}
}
}
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec(v_a_1528_);
lean_dec(v_numIndices_1525_);
lean_dec(v_numParams_1524_);
lean_dec_ref(v_toConstantVal_1523_);
lean_dec(v_us_1509_);
v___x_1581_ = lean_box(0);
v___x_1582_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1581_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1582_;
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_numIndices_1525_);
lean_dec(v_numParams_1524_);
lean_dec_ref(v_toConstantVal_1523_);
lean_dec(v_us_1509_);
lean_dec(v_a_1506_);
lean_dec_ref(v_e_1497_);
lean_dec(v_idx_1496_);
lean_dec(v_structName_1495_);
v_a_1583_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1527_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1527_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1521_, 2);
lean_dec_ref(v_val_1520_);
lean_dec(v_us_1509_);
goto v___jp_1511_;
}
}
else
{
lean_dec(v_ctors_1521_);
lean_dec_ref(v_val_1520_);
lean_dec(v_us_1509_);
goto v___jp_1511_;
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_val_1519_);
lean_dec(v_us_1509_);
v___x_1591_ = lean_box(0);
v___x_1592_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1591_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1592_;
}
}
v___jp_1511_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1512_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec_ref(v___x_1507_);
v___x_1593_ = lean_box(0);
v___x_1594_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1495_, v_idx_1496_, v_e_1497_, v_a_1506_, lean_box(0), v___x_1593_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1594_;
}
}
else
{
lean_dec_ref(v_e_1497_);
lean_dec(v_idx_1496_);
lean_dec(v_structName_1495_);
return v___x_1505_;
}
}
else
{
lean_dec_ref(v_e_1497_);
lean_dec(v_idx_1496_);
lean_dec(v_structName_1495_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1595_, lean_object* v_idx_1596_, lean_object* v_e_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1595_, v_idx_1596_, v_e_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1604_, lean_object* v_structName_1605_, lean_object* v_e_1606_, lean_object* v_idx_1607_, lean_object* v_a_1608_, lean_object* v_inst_1609_, lean_object* v_R_1610_, lean_object* v_a_1611_, lean_object* v_b_1612_, lean_object* v_c_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1604_, v_structName_1605_, v_e_1606_, v_idx_1607_, v_a_1608_, v_a_1611_, v_b_1612_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1620_, lean_object* v_structName_1621_, lean_object* v_e_1622_, lean_object* v_idx_1623_, lean_object* v_a_1624_, lean_object* v_inst_1625_, lean_object* v_R_1626_, lean_object* v_a_1627_, lean_object* v_b_1628_, lean_object* v_c_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1620_, v_structName_1621_, v_e_1622_, v_idx_1623_, v_a_1624_, v_inst_1625_, v_R_1626_, v_a_1627_, v_b_1628_, v_c_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v_upperBound_1620_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1636_, lean_object* v_structName_1637_, lean_object* v_e_1638_, lean_object* v_idx_1639_, lean_object* v_a_1640_, lean_object* v_inst_1641_, lean_object* v_R_1642_, lean_object* v_a_1643_, lean_object* v_b_1644_, lean_object* v_c_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1636_, v_structName_1637_, v_e_1638_, v_idx_1639_, v_a_1640_, v_a_1643_, v_b_1644_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1652_, lean_object* v_structName_1653_, lean_object* v_e_1654_, lean_object* v_idx_1655_, lean_object* v_a_1656_, lean_object* v_inst_1657_, lean_object* v_R_1658_, lean_object* v_a_1659_, lean_object* v_b_1660_, lean_object* v_c_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1652_, v_structName_1653_, v_e_1654_, v_idx_1655_, v_a_1656_, v_inst_1657_, v_R_1658_, v_a_1659_, v_b_1660_, v_c_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v_upperBound_1652_);
return v_res_1667_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1670_ = l_Lean_stringToMessageData(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1678_ = l_Lean_indentExpr(v_type_1671_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1679_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1688_, lean_object* v_type_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_type_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1696_, v_type_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_ks_1708_; lean_object* v_vs_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1733_; 
v_ks_1708_ = lean_ctor_get(v_x_1704_, 0);
v_vs_1709_ = lean_ctor_get(v_x_1704_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_x_1704_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1711_ = v_x_1704_;
v_isShared_1712_ = v_isSharedCheck_1733_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_vs_1709_);
lean_inc(v_ks_1708_);
lean_dec(v_x_1704_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1733_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = lean_array_get_size(v_ks_1708_);
v___x_1714_ = lean_nat_dec_lt(v_x_1705_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_dec(v_x_1705_);
v___x_1715_ = lean_array_push(v_ks_1708_, v_x_1706_);
v___x_1716_ = lean_array_push(v_vs_1709_, v_x_1707_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1716_);
lean_ctor_set(v___x_1711_, 0, v___x_1715_);
v___x_1718_ = v___x_1711_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_object* v_k_x27_1720_; uint8_t v___x_1721_; 
v_k_x27_1720_ = lean_array_fget_borrowed(v_ks_1708_, v_x_1705_);
v___x_1721_ = l_Lean_instBEqMVarId_beq(v_x_1706_, v_k_x27_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1723_; 
if (v_isShared_1712_ == 0)
{
v___x_1723_ = v___x_1711_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_ks_1708_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_vs_1709_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_nat_add(v_x_1705_, v___x_1724_);
lean_dec(v_x_1705_);
v_x_1704_ = v___x_1723_;
v_x_1705_ = v___x_1725_;
goto _start;
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1728_ = lean_array_fset(v_ks_1708_, v_x_1705_, v_x_1706_);
v___x_1729_ = lean_array_fset(v_vs_1709_, v_x_1705_, v_x_1707_);
lean_dec(v_x_1705_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1729_);
lean_ctor_set(v___x_1711_, 0, v___x_1728_);
v___x_1731_ = v___x_1711_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1734_, lean_object* v_k_1735_, lean_object* v_v_1736_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1734_, v___x_1737_, v_k_1735_, v_v_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1740_, size_t v_x_1741_, size_t v_x_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 0)
{
lean_object* v_es_1745_; size_t v___x_1746_; size_t v___x_1747_; lean_object* v_j_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_es_1745_ = lean_ctor_get(v_x_1740_, 0);
v___x_1746_ = ((size_t)31ULL);
v___x_1747_ = lean_usize_land(v_x_1741_, v___x_1746_);
v_j_1748_ = lean_usize_to_nat(v___x_1747_);
v___x_1749_ = lean_array_get_size(v_es_1745_);
v___x_1750_ = lean_nat_dec_lt(v_j_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec(v_j_1748_);
lean_dec(v_x_1744_);
lean_dec(v_x_1743_);
return v_x_1740_;
}
else
{
lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1789_; 
lean_inc_ref(v_es_1745_);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_x_1740_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v_x_1740_, 0);
lean_dec(v_unused_1790_);
v___x_1752_ = v_x_1740_;
v_isShared_1753_ = v_isSharedCheck_1789_;
goto v_resetjp_1751_;
}
else
{
lean_dec(v_x_1740_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1789_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_v_1754_; lean_object* v___x_1755_; lean_object* v_xs_x27_1756_; lean_object* v___y_1758_; 
v_v_1754_ = lean_array_fget(v_es_1745_, v_j_1748_);
v___x_1755_ = lean_box(0);
v_xs_x27_1756_ = lean_array_fset(v_es_1745_, v_j_1748_, v___x_1755_);
switch(lean_obj_tag(v_v_1754_))
{
case 0:
{
lean_object* v_key_1763_; lean_object* v_val_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1774_; 
v_key_1763_ = lean_ctor_get(v_v_1754_, 0);
v_val_1764_ = lean_ctor_get(v_v_1754_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_v_1754_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1766_ = v_v_1754_;
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_val_1764_);
lean_inc(v_key_1763_);
lean_dec(v_v_1754_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1774_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
uint8_t v___x_1768_; 
v___x_1768_ = l_Lean_instBEqMVarId_beq(v_x_1743_, v_key_1763_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_del_object(v___x_1766_);
v___x_1769_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1763_, v_val_1764_, v_x_1743_, v_x_1744_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
v___y_1758_ = v___x_1770_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1772_; 
lean_dec(v_val_1764_);
lean_dec(v_key_1763_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v_x_1744_);
lean_ctor_set(v___x_1766_, 0, v_x_1743_);
v___x_1772_ = v___x_1766_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_x_1743_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_x_1744_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
v___y_1758_ = v___x_1772_;
goto v___jp_1757_;
}
}
}
}
case 1:
{
lean_object* v_node_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1787_; 
v_node_1775_ = lean_ctor_get(v_v_1754_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_v_1754_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1777_ = v_v_1754_;
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_node_1775_);
lean_dec(v_v_1754_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1787_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
size_t v___x_1779_; size_t v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1779_ = ((size_t)5ULL);
v___x_1780_ = lean_usize_shift_right(v_x_1741_, v___x_1779_);
v___x_1781_ = ((size_t)1ULL);
v___x_1782_ = lean_usize_add(v_x_1742_, v___x_1781_);
v___x_1783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1775_, v___x_1780_, v___x_1782_, v_x_1743_, v_x_1744_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1783_);
v___x_1785_ = v___x_1777_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v___y_1758_ = v___x_1785_;
goto v___jp_1757_;
}
}
}
default: 
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_x_1743_);
lean_ctor_set(v___x_1788_, 1, v_x_1744_);
v___y_1758_ = v___x_1788_;
goto v___jp_1757_;
}
}
v___jp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_array_fset(v_xs_x27_1756_, v_j_1748_, v___y_1758_);
lean_dec(v_j_1748_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1759_);
v___x_1761_ = v___x_1752_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
else
{
lean_object* v_ks_1791_; lean_object* v_vs_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1810_; 
v_ks_1791_ = lean_ctor_get(v_x_1740_, 0);
v_vs_1792_ = lean_ctor_get(v_x_1740_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_x_1740_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1794_ = v_x_1740_;
v_isShared_1795_ = v_isSharedCheck_1810_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_vs_1792_);
lean_inc(v_ks_1791_);
lean_dec(v_x_1740_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1810_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_ks_1791_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_vs_1792_);
v___x_1797_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v_newNode_1798_; size_t v___x_1799_; uint8_t v___x_1800_; 
v_newNode_1798_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1797_, v_x_1743_, v_x_1744_);
v___x_1799_ = ((size_t)7ULL);
v___x_1800_ = lean_usize_dec_le(v___x_1799_, v_x_1742_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1798_);
v___x_1802_ = lean_unsigned_to_nat(4u);
v___x_1803_ = lean_nat_dec_lt(v___x_1801_, v___x_1802_);
lean_dec(v___x_1801_);
if (v___x_1803_ == 0)
{
lean_object* v_ks_1804_; lean_object* v_vs_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_ks_1804_ = lean_ctor_get(v_newNode_1798_, 0);
lean_inc_ref(v_ks_1804_);
v_vs_1805_ = lean_ctor_get(v_newNode_1798_, 1);
lean_inc_ref(v_vs_1805_);
lean_dec_ref(v_newNode_1798_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1742_, v_ks_1804_, v_vs_1805_, v___x_1806_, v___x_1807_);
lean_dec_ref(v_vs_1805_);
lean_dec_ref(v_ks_1804_);
return v___x_1808_;
}
else
{
return v_newNode_1798_;
}
}
else
{
return v_newNode_1798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1811_, lean_object* v_keys_1812_, lean_object* v_vals_1813_, lean_object* v_i_1814_, lean_object* v_entries_1815_){
_start:
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_array_get_size(v_keys_1812_);
v___x_1817_ = lean_nat_dec_lt(v_i_1814_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec(v_i_1814_);
return v_entries_1815_;
}
else
{
lean_object* v_k_1818_; lean_object* v_v_1819_; uint64_t v___x_1820_; size_t v_h_1821_; size_t v___x_1822_; lean_object* v___x_1823_; size_t v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; size_t v_h_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_k_1818_ = lean_array_fget_borrowed(v_keys_1812_, v_i_1814_);
v_v_1819_ = lean_array_fget_borrowed(v_vals_1813_, v_i_1814_);
v___x_1820_ = l_Lean_instHashableMVarId_hash(v_k_1818_);
v_h_1821_ = lean_uint64_to_usize(v___x_1820_);
v___x_1822_ = ((size_t)5ULL);
v___x_1823_ = lean_unsigned_to_nat(1u);
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = lean_usize_sub(v_depth_1811_, v___x_1824_);
v___x_1826_ = lean_usize_mul(v___x_1822_, v___x_1825_);
v_h_1827_ = lean_usize_shift_right(v_h_1821_, v___x_1826_);
v___x_1828_ = lean_nat_add(v_i_1814_, v___x_1823_);
lean_dec(v_i_1814_);
lean_inc(v_v_1819_);
lean_inc(v_k_1818_);
v___x_1829_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1815_, v_h_1827_, v_depth_1811_, v_k_1818_, v_v_1819_);
v_i_1814_ = v___x_1828_;
v_entries_1815_ = v___x_1829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1831_, lean_object* v_keys_1832_, lean_object* v_vals_1833_, lean_object* v_i_1834_, lean_object* v_entries_1835_){
_start:
{
size_t v_depth_boxed_1836_; lean_object* v_res_1837_; 
v_depth_boxed_1836_ = lean_unbox_usize(v_depth_1831_);
lean_dec(v_depth_1831_);
v_res_1837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1836_, v_keys_1832_, v_vals_1833_, v_i_1834_, v_entries_1835_);
lean_dec_ref(v_vals_1833_);
lean_dec_ref(v_keys_1832_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
size_t v_x_1155__boxed_1843_; size_t v_x_1156__boxed_1844_; lean_object* v_res_1845_; 
v_x_1155__boxed_1843_ = lean_unbox_usize(v_x_1839_);
lean_dec(v_x_1839_);
v_x_1156__boxed_1844_ = lean_unbox_usize(v_x_1840_);
lean_dec(v_x_1840_);
v_res_1845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1838_, v_x_1155__boxed_1843_, v_x_1156__boxed_1844_, v_x_1841_, v_x_1842_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_){
_start:
{
uint64_t v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = l_Lean_instHashableMVarId_hash(v_x_1847_);
v___x_1850_ = lean_uint64_to_usize(v___x_1849_);
v___x_1851_ = ((size_t)1ULL);
v___x_1852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1846_, v___x_1850_, v___x_1851_, v_x_1847_, v_x_1848_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1853_, lean_object* v_val_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v_mctx_1858_; lean_object* v_cache_1859_; lean_object* v_zetaDeltaFVarIds_1860_; lean_object* v_postponed_1861_; lean_object* v_diag_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1892_; 
v___x_1857_ = lean_st_ref_take(v___y_1855_);
v_mctx_1858_ = lean_ctor_get(v___x_1857_, 0);
v_cache_1859_ = lean_ctor_get(v___x_1857_, 1);
v_zetaDeltaFVarIds_1860_ = lean_ctor_get(v___x_1857_, 2);
v_postponed_1861_ = lean_ctor_get(v___x_1857_, 3);
v_diag_1862_ = lean_ctor_get(v___x_1857_, 4);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1864_ = v___x_1857_;
v_isShared_1865_ = v_isSharedCheck_1892_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_diag_1862_);
lean_inc(v_postponed_1861_);
lean_inc(v_zetaDeltaFVarIds_1860_);
lean_inc(v_cache_1859_);
lean_inc(v_mctx_1858_);
lean_dec(v___x_1857_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1892_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_depth_1866_; lean_object* v_levelAssignDepth_1867_; lean_object* v_lmvarCounter_1868_; lean_object* v_mvarCounter_1869_; lean_object* v_lDecls_1870_; lean_object* v_decls_1871_; lean_object* v_userNames_1872_; lean_object* v_lAssignment_1873_; lean_object* v_eAssignment_1874_; lean_object* v_dAssignment_1875_; lean_object* v_instanceTypedMVars_1876_; lean_object* v_synthNormMemo_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1891_; 
v_depth_1866_ = lean_ctor_get(v_mctx_1858_, 0);
v_levelAssignDepth_1867_ = lean_ctor_get(v_mctx_1858_, 1);
v_lmvarCounter_1868_ = lean_ctor_get(v_mctx_1858_, 2);
v_mvarCounter_1869_ = lean_ctor_get(v_mctx_1858_, 3);
v_lDecls_1870_ = lean_ctor_get(v_mctx_1858_, 4);
v_decls_1871_ = lean_ctor_get(v_mctx_1858_, 5);
v_userNames_1872_ = lean_ctor_get(v_mctx_1858_, 6);
v_lAssignment_1873_ = lean_ctor_get(v_mctx_1858_, 7);
v_eAssignment_1874_ = lean_ctor_get(v_mctx_1858_, 8);
v_dAssignment_1875_ = lean_ctor_get(v_mctx_1858_, 9);
v_instanceTypedMVars_1876_ = lean_ctor_get(v_mctx_1858_, 10);
v_synthNormMemo_1877_ = lean_ctor_get(v_mctx_1858_, 11);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_mctx_1858_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1879_ = v_mctx_1858_;
v_isShared_1880_ = v_isSharedCheck_1891_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_synthNormMemo_1877_);
lean_inc(v_instanceTypedMVars_1876_);
lean_inc(v_dAssignment_1875_);
lean_inc(v_eAssignment_1874_);
lean_inc(v_lAssignment_1873_);
lean_inc(v_userNames_1872_);
lean_inc(v_decls_1871_);
lean_inc(v_lDecls_1870_);
lean_inc(v_mvarCounter_1869_);
lean_inc(v_lmvarCounter_1868_);
lean_inc(v_levelAssignDepth_1867_);
lean_inc(v_depth_1866_);
lean_dec(v_mctx_1858_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1891_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1881_ = lean_box(0);
v___x_1882_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1874_, v_mvarId_1853_, v_val_1854_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 8, v___x_1882_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_depth_1866_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_levelAssignDepth_1867_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_lmvarCounter_1868_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_mvarCounter_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_lDecls_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_decls_1871_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_userNames_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_lAssignment_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1890_, 9, v_dAssignment_1875_);
lean_ctor_set(v_reuseFailAlloc_1890_, 10, v_instanceTypedMVars_1876_);
lean_ctor_set(v_reuseFailAlloc_1890_, 11, v_synthNormMemo_1877_);
v___x_1884_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1884_);
v___x_1886_ = v___x_1864_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_cache_1859_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_zetaDeltaFVarIds_1860_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_postponed_1861_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v_diag_1862_);
v___x_1886_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_st_ref_put(v___y_1855_, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1881_);
return v___x_1888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1893_, lean_object* v_val_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1893_, v_val_1894_, v___y_1895_);
lean_dec(v___y_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; 
lean_inc(v_a_1902_);
lean_inc_ref(v_a_1901_);
lean_inc(v_a_1900_);
lean_inc_ref(v_a_1899_);
lean_inc_ref(v_type_1898_);
v___x_1904_ = lean_infer_type(v_type_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = l_Lean_Meta_whnfD(v_a_1905_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1941_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1941_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1941_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
switch(lean_obj_tag(v_a_1907_))
{
case 3:
{
lean_object* v_u_1911_; lean_object* v___x_1913_; 
lean_dec_ref(v_type_1898_);
v_u_1911_ = lean_ctor_get(v_a_1907_, 0);
lean_inc(v_u_1911_);
lean_dec_ref_known(v_a_1907_, 1);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_u_1911_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_u_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
case 2:
{
lean_object* v_mvarId_1915_; lean_object* v___x_1916_; 
lean_del_object(v___x_1909_);
v_mvarId_1915_ = lean_ctor_get(v_a_1907_, 0);
lean_inc_n(v_mvarId_1915_, 2);
lean_dec_ref_known(v_a_1907_, 1);
v___x_1916_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1915_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; uint8_t v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = lean_unbox(v_a_1917_);
lean_dec(v_a_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
lean_dec_ref(v_type_1898_);
v___x_1919_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc_n(v_a_1920_, 2);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_mkSort(v_a_1920_);
v___x_1922_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1915_, v___x_1921_, v_a_1900_);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v___x_1922_, 0);
lean_dec(v_unused_1930_);
v___x_1924_ = v___x_1922_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_dec(v___x_1922_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_a_1920_);
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1920_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_dec(v_mvarId_1915_);
return v___x_1919_;
}
}
else
{
lean_object* v___x_1931_; 
lean_dec(v_mvarId_1915_);
v___x_1931_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1931_;
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_mvarId_1915_);
lean_dec_ref(v_type_1898_);
v_a_1932_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1916_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1916_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
default: 
{
lean_object* v___x_1940_; 
lean_del_object(v___x_1909_);
lean_dec(v_a_1907_);
v___x_1940_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_type_1898_);
v_a_1942_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1906_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1906_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_type_1898_);
v_a_1950_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1904_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1904_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Meta_getLevel(v_type_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1965_, lean_object* v_val_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1965_, v_val_1966_, v___y_1968_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1973_, lean_object* v_val_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1973_, v_val_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1982_, v_x_1983_, v_x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1986_, lean_object* v_x_1987_, size_t v_x_1988_, size_t v_x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1987_, v_x_1988_, v_x_1989_, v_x_1990_, v_x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
size_t v_x_1504__boxed_1999_; size_t v_x_1505__boxed_2000_; lean_object* v_res_2001_; 
v_x_1504__boxed_1999_ = lean_unbox_usize(v_x_1995_);
lean_dec(v_x_1995_);
v_x_1505__boxed_2000_ = lean_unbox_usize(v_x_1996_);
lean_dec(v_x_1996_);
v_res_2001_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_1993_, v_x_1994_, v_x_1504__boxed_1999_, v_x_1505__boxed_2000_, v_x_1997_, v_x_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2002_, lean_object* v_n_2003_, lean_object* v_k_2004_, lean_object* v_v_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2003_, v_k_2004_, v_v_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2007_, size_t v_depth_2008_, lean_object* v_keys_2009_, lean_object* v_vals_2010_, lean_object* v_heq_2011_, lean_object* v_i_2012_, lean_object* v_entries_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2008_, v_keys_2009_, v_vals_2010_, v_i_2012_, v_entries_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2015_, lean_object* v_depth_2016_, lean_object* v_keys_2017_, lean_object* v_vals_2018_, lean_object* v_heq_2019_, lean_object* v_i_2020_, lean_object* v_entries_2021_){
_start:
{
size_t v_depth_boxed_2022_; lean_object* v_res_2023_; 
v_depth_boxed_2022_ = lean_unbox_usize(v_depth_2016_);
lean_dec(v_depth_2016_);
v_res_2023_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2015_, v_depth_boxed_2022_, v_keys_2017_, v_vals_2018_, v_heq_2019_, v_i_2020_, v_entries_2021_);
lean_dec_ref(v_vals_2018_);
lean_dec_ref(v_keys_2017_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2025_, v_x_2026_, v_x_2027_, v_x_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2030_, lean_object* v_b_2031_, lean_object* v_c_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; 
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
v___x_2038_ = lean_apply_7(v_k_2030_, v_b_2031_, v_c_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, lean_box(0));
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2039_, lean_object* v_b_2040_, lean_object* v_c_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2039_, v_b_2040_, v_c_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2048_, lean_object* v_k_2049_, uint8_t v_cleanupAnnotations_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___f_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___f_2056_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2056_, 0, v_k_2049_);
v___x_2057_ = 0;
v___x_2058_ = lean_box(0);
v___x_2059_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2057_, v___x_2058_, v_type_2048_, v___f_2056_, v_cleanupAnnotations_2050_, v___x_2057_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_a_2068_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2059_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2059_);
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
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2076_, lean_object* v_k_2077_, lean_object* v_cleanupAnnotations_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2084_; lean_object* v_res_2085_; 
v_cleanupAnnotations_boxed_2084_ = lean_unbox(v_cleanupAnnotations_2078_);
v_res_2085_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2076_, v_k_2077_, v_cleanupAnnotations_boxed_2084_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2086_, lean_object* v_type_2087_, lean_object* v_k_2088_, uint8_t v_cleanupAnnotations_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2087_, v_k_2088_, v_cleanupAnnotations_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2096_, lean_object* v_type_2097_, lean_object* v_k_2098_, lean_object* v_cleanupAnnotations_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2105_; lean_object* v_res_2106_; 
v_cleanupAnnotations_boxed_2105_ = lean_unbox(v_cleanupAnnotations_2099_);
v_res_2106_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2096_, v_type_2097_, v_k_2098_, v_cleanupAnnotations_boxed_2105_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2107_, size_t v_i_2108_, size_t v_stop_2109_, lean_object* v_b_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_usize_dec_eq(v_i_2108_, v_stop_2109_);
if (v___x_2116_ == 0)
{
size_t v___x_2117_; size_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = ((size_t)1ULL);
v___x_2118_ = lean_usize_sub(v_i_2108_, v___x_2117_);
v___x_2119_ = lean_array_uget_borrowed(v_as_2107_, v___x_2118_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___x_2119_);
v___x_2120_ = lean_infer_type(v___x_2119_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = l_Lean_Meta_getLevel(v_a_2121_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = l_Lean_mkLevelIMax_x27(v_a_2123_, v_b_2110_);
v_i_2108_ = v___x_2118_;
v_b_2110_ = v___x_2124_;
goto _start;
}
else
{
lean_dec(v_b_2110_);
return v___x_2122_;
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_b_2110_);
v_a_2126_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2120_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2120_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_b_2110_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2135_, lean_object* v_i_2136_, lean_object* v_stop_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
size_t v_i_boxed_2144_; size_t v_stop_boxed_2145_; lean_object* v_res_2146_; 
v_i_boxed_2144_ = lean_unbox_usize(v_i_2136_);
lean_dec(v_i_2136_);
v_stop_boxed_2145_ = lean_unbox_usize(v_stop_2137_);
lean_dec(v_stop_2137_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2135_, v_i_boxed_2144_, v_stop_boxed_2145_, v_b_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec_ref(v_as_2135_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2147_, lean_object* v_e_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_a_2155_; lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Meta_getLevel(v_e_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = lean_array_get_size(v_xs_2147_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v___x_2163_ = lean_nat_dec_lt(v___x_2162_, v___x_2161_);
if (v___x_2163_ == 0)
{
v_a_2155_ = v_a_2160_;
goto v___jp_2154_;
}
else
{
size_t v___x_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_usize_of_nat(v___x_2161_);
v___x_2165_ = ((size_t)0ULL);
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2147_, v___x_2164_, v___x_2165_, v_a_2160_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v_a_2155_ = v_a_2167_;
goto v___jp_2154_;
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_a_2168_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2166_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2166_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_a_2176_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2159_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2159_);
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
v___jp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = l_Lean_Level_normalize(v_a_2155_);
lean_dec(v_a_2155_);
v___x_2157_ = l_Lean_mkSort(v___x_2156_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2184_, lean_object* v_e_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2184_, v_e_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_xs_2184_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___f_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; 
v___f_2199_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2200_ = 0;
v___x_2201_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2193_, v___f_2199_, v___x_2200_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2209_, lean_object* v_k_2210_, uint8_t v_cleanupAnnotations_2211_, uint8_t v_preserveNondepLet_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___f_2218_; uint8_t v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2218_, 0, v_k_2210_);
v___x_2219_ = 1;
v___x_2220_ = 0;
v___x_2221_ = lean_box(0);
v___x_2222_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2209_, v___x_2219_, v___x_2219_, v_preserveNondepLet_2212_, v___x_2220_, v___x_2221_, v___f_2218_, v_cleanupAnnotations_2211_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_a_2231_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2222_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2222_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2239_, lean_object* v_k_2240_, lean_object* v_cleanupAnnotations_2241_, lean_object* v_preserveNondepLet_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2248_; uint8_t v_preserveNondepLet_boxed_2249_; lean_object* v_res_2250_; 
v_cleanupAnnotations_boxed_2248_ = lean_unbox(v_cleanupAnnotations_2241_);
v_preserveNondepLet_boxed_2249_ = lean_unbox(v_preserveNondepLet_2242_);
v_res_2250_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2239_, v_k_2240_, v_cleanupAnnotations_boxed_2248_, v_preserveNondepLet_boxed_2249_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2251_, lean_object* v_e_2252_, lean_object* v_k_2253_, uint8_t v_cleanupAnnotations_2254_, uint8_t v_preserveNondepLet_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2252_, v_k_2253_, v_cleanupAnnotations_2254_, v_preserveNondepLet_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2262_, lean_object* v_e_2263_, lean_object* v_k_2264_, lean_object* v_cleanupAnnotations_2265_, lean_object* v_preserveNondepLet_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2272_; uint8_t v_preserveNondepLet_boxed_2273_; lean_object* v_res_2274_; 
v_cleanupAnnotations_boxed_2272_ = lean_unbox(v_cleanupAnnotations_2265_);
v_preserveNondepLet_boxed_2273_ = lean_unbox(v_preserveNondepLet_2266_);
v_res_2274_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2262_, v_e_2263_, v_k_2264_, v_cleanupAnnotations_boxed_2272_, v_preserveNondepLet_boxed_2273_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2275_, lean_object* v_e_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; 
lean_inc(v___y_2280_);
lean_inc_ref(v___y_2279_);
lean_inc(v___y_2278_);
lean_inc_ref(v___y_2277_);
v___x_2282_ = lean_infer_type(v_e_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; uint8_t v___x_2284_; uint8_t v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2284_ = 0;
v___x_2285_ = 1;
v___x_2286_ = 1;
v___x_2287_ = l_Lean_Meta_mkForallFVars(v_xs_2275_, v_a_2283_, v___x_2284_, v___x_2285_, v___x_2284_, v___x_2286_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v___x_2287_;
}
else
{
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2288_, lean_object* v_e_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2288_, v_e_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec_ref(v_xs_2288_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___f_2303_; uint8_t v___x_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; 
v___f_2303_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2304_ = 0;
v___x_2305_ = 1;
v___x_2306_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2297_, v___f_2303_, v___x_2304_, v___x_2305_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2313_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2326_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2327_ = l_Lean_MessageData_ofName(v_mvarId_2320_);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2330_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2339_, lean_object* v_mvarId_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_mvarId_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2347_, v_mvarId_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; lean_object* v_mctx_2362_; lean_object* v___x_2363_; 
v___x_2361_ = lean_st_ref_get(v_a_2357_);
v_mctx_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc_ref(v_mctx_2362_);
lean_dec(v___x_2361_);
v___x_2363_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2362_, v_mvarId_2355_);
lean_dec_ref(v_mctx_2362_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
return v___x_2364_;
}
else
{
lean_object* v_val_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_mvarId_2355_);
v_val_2365_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2367_ = v___x_2363_;
v_isShared_2368_ = v_isSharedCheck_2373_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_val_2365_);
lean_dec(v___x_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2373_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v_type_2369_; lean_object* v___x_2371_; 
v_type_2369_ = lean_ctor_get(v_val_2365_, 2);
lean_inc_ref(v_type_2369_);
lean_dec(v_val_2365_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set_tag(v___x_2367_, 0);
lean_ctor_set(v___x_2367_, 0, v_type_2369_);
v___x_2371_ = v___x_2367_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_type_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_lctx_2386_; lean_object* v___x_2387_; 
v_lctx_2386_ = lean_ctor_get(v_a_2382_, 2);
lean_inc(v_fvarId_2381_);
lean_inc_ref(v_lctx_2386_);
v___x_2387_ = lean_local_ctx_find(v_lctx_2386_, v_fvarId_2381_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2381_, v_a_2383_, v_a_2384_);
return v___x_2388_;
}
else
{
lean_object* v_val_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_fvarId_2381_);
v_val_2389_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2391_ = v___x_2387_;
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_val_2389_);
lean_dec(v___x_2387_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = l_Lean_LocalDecl_type(v_val_2389_);
lean_dec(v_val_2389_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2393_);
v___x_2395_ = v___x_2391_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2404_, v_a_2405_, v_a_2407_, v_a_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2417_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_instMonadEIO___redArg();
return v___x_2418_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2420_ = l_StateRefT_x27_instMonad___redArg(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_instMonadExceptOfEIO___redArg();
return v___x_2423_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___f_2425_; 
v___x_2424_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2425_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2425_, 0, v___x_2424_);
return v___f_2425_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___f_2427_; 
v___x_2426_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2427_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2427_, 0, v___x_2426_);
return v___f_2427_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; 
v___f_2428_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2429_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___f_2429_);
lean_ctor_set(v___x_2430_, 1, v___f_2428_);
return v___x_2430_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___f_2432_; 
v___x_2431_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2432_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2432_, 0, v___x_2431_);
return v___f_2432_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___f_2434_; 
v___x_2433_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2434_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2434_, 0, v___x_2433_);
return v___f_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; 
v___f_2435_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2436_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___f_2436_);
lean_ctor_set(v___x_2437_, 1, v___f_2435_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2440_, lean_object* v_inferType_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
uint8_t v_cacheInferType_2486_; 
v_cacheInferType_2486_ = lean_ctor_get_uint8(v_a_2442_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2486_ == 0)
{
lean_dec_ref(v_e_2440_);
goto v___jp_2447_;
}
else
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Lean_Expr_hasMVar(v_e_2440_);
if (v___x_2487_ == 0)
{
lean_object* v___f_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___f_2488_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2490_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2440_, v_a_2442_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2588_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2588_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2588_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2535_; lean_object* v_cache_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2583_; 
v___x_2535_ = lean_st_ref_get(v_a_2443_);
v_cache_2536_ = lean_ctor_get(v___x_2535_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; lean_object* v_unused_2587_; 
v_unused_2584_ = lean_ctor_get(v___x_2535_, 4);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v___x_2535_, 3);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v___x_2535_, 2);
lean_dec(v_unused_2586_);
v_unused_2587_ = lean_ctor_get(v___x_2535_, 0);
lean_dec(v_unused_2587_);
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2583_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_cache_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2583_;
goto v_resetjp_2537_;
}
v___jp_2495_:
{
lean_object* v___x_2496_; 
lean_inc(v_a_2445_);
lean_inc_ref(v_a_2444_);
lean_inc(v_a_2443_);
lean_inc_ref(v_a_2442_);
v___x_2496_ = lean_apply_5(v_inferType_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, lean_box(0));
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; uint8_t v___x_2498_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
v___x_2498_ = l_Lean_Expr_hasMVar(v_a_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2533_; 
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2496_, 0);
lean_dec(v_unused_2534_);
v___x_2500_ = v___x_2496_;
v_isShared_2501_ = v_isSharedCheck_2533_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v___x_2496_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2533_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v_cache_2503_; lean_object* v_mctx_2504_; lean_object* v_zetaDeltaFVarIds_2505_; lean_object* v_postponed_2506_; lean_object* v_diag_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2532_; 
v___x_2502_ = lean_st_ref_take(v_a_2443_);
v_cache_2503_ = lean_ctor_get(v___x_2502_, 1);
v_mctx_2504_ = lean_ctor_get(v___x_2502_, 0);
v_zetaDeltaFVarIds_2505_ = lean_ctor_get(v___x_2502_, 2);
v_postponed_2506_ = lean_ctor_get(v___x_2502_, 3);
v_diag_2507_ = lean_ctor_get(v___x_2502_, 4);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2509_ = v___x_2502_;
v_isShared_2510_ = v_isSharedCheck_2532_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_diag_2507_);
lean_inc(v_postponed_2506_);
lean_inc(v_zetaDeltaFVarIds_2505_);
lean_inc(v_cache_2503_);
lean_inc(v_mctx_2504_);
lean_dec(v___x_2502_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2532_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_inferType_2511_; lean_object* v_funInfo_2512_; lean_object* v_synthInstance_2513_; lean_object* v_whnf_2514_; lean_object* v_defEqTrans_2515_; lean_object* v_defEqPerm_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2531_; 
v_inferType_2511_ = lean_ctor_get(v_cache_2503_, 0);
v_funInfo_2512_ = lean_ctor_get(v_cache_2503_, 1);
v_synthInstance_2513_ = lean_ctor_get(v_cache_2503_, 2);
v_whnf_2514_ = lean_ctor_get(v_cache_2503_, 3);
v_defEqTrans_2515_ = lean_ctor_get(v_cache_2503_, 4);
v_defEqPerm_2516_ = lean_ctor_get(v_cache_2503_, 5);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_cache_2503_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2518_ = v_cache_2503_;
v_isShared_2519_ = v_isSharedCheck_2531_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_defEqPerm_2516_);
lean_inc(v_defEqTrans_2515_);
lean_inc(v_whnf_2514_);
lean_inc(v_synthInstance_2513_);
lean_inc(v_funInfo_2512_);
lean_inc(v_inferType_2511_);
lean_dec(v_cache_2503_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2531_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
lean_inc(v_a_2497_);
v___x_2520_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2488_, v___x_2489_, v_inferType_2511_, v_a_2491_, v_a_2497_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_funInfo_2512_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_synthInstance_2513_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_whnf_2514_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_defEqTrans_2515_);
lean_ctor_set(v_reuseFailAlloc_2530_, 5, v_defEqPerm_2516_);
v___x_2522_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2524_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v___x_2522_);
v___x_2524_ = v___x_2509_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_mctx_2504_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_zetaDeltaFVarIds_2505_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_postponed_2506_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_diag_2507_);
v___x_2524_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = lean_st_ref_put(v_a_2443_, v___x_2524_);
if (v_isShared_2501_ == 0)
{
v___x_2527_ = v___x_2500_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2497_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2497_);
lean_dec(v_a_2491_);
return v___x_2496_;
}
}
else
{
lean_dec(v_a_2491_);
return v___x_2496_;
}
}
v_resetjp_2537_:
{
lean_object* v_inferType_2540_; lean_object* v___x_2541_; 
v_inferType_2540_ = lean_ctor_get(v_cache_2536_, 0);
lean_inc_ref(v_inferType_2540_);
lean_dec_ref(v_cache_2536_);
lean_inc(v_a_2491_);
v___x_2541_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2488_, v___x_2489_, v_inferType_2540_, v_a_2491_);
lean_dec_ref(v_inferType_2540_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; lean_object* v_toApplicative_2543_; lean_object* v_toFunctor_2544_; lean_object* v_toSeq_2545_; lean_object* v_toSeqLeft_2546_; lean_object* v_toSeqRight_2547_; lean_object* v___f_2548_; lean_object* v___f_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___x_2552_; lean_object* v___f_2553_; lean_object* v___f_2554_; lean_object* v___f_2555_; lean_object* v___x_2557_; 
lean_del_object(v___x_2493_);
v___x_2542_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2543_ = lean_ctor_get(v___x_2542_, 0);
v_toFunctor_2544_ = lean_ctor_get(v_toApplicative_2543_, 0);
v_toSeq_2545_ = lean_ctor_get(v_toApplicative_2543_, 2);
v_toSeqLeft_2546_ = lean_ctor_get(v_toApplicative_2543_, 3);
v_toSeqRight_2547_ = lean_ctor_get(v_toApplicative_2543_, 4);
v___f_2548_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2549_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2544_, 2);
v___f_2550_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2550_, 0, v_toFunctor_2544_);
v___f_2551_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2551_, 0, v_toFunctor_2544_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___f_2550_);
lean_ctor_set(v___x_2552_, 1, v___f_2551_);
lean_inc(v_toSeqRight_2547_);
v___f_2553_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2553_, 0, v_toSeqRight_2547_);
lean_inc(v_toSeqLeft_2546_);
v___f_2554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2554_, 0, v_toSeqLeft_2546_);
lean_inc(v_toSeq_2545_);
v___f_2555_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2555_, 0, v_toSeq_2545_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 4, v___f_2553_);
lean_ctor_set(v___x_2538_, 3, v___f_2554_);
lean_ctor_set(v___x_2538_, 2, v___f_2555_);
lean_ctor_set(v___x_2538_, 1, v___f_2548_);
lean_ctor_set(v___x_2538_, 0, v___x_2552_);
v___x_2557_ = v___x_2538_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___f_2548_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v___f_2555_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v___f_2554_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v___f_2553_);
v___x_2557_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_toCold_2564_; lean_object* v_cancelTk_x3f_2565_; 
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
lean_ctor_set(v___x_2558_, 1, v___f_2549_);
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2560_ = l_Lean_Core_instMonadRefCoreM;
v___x_2561_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2562_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2561_, v___x_2558_);
v___x_2563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2559_);
lean_ctor_set(v___x_2563_, 1, v___x_2560_);
lean_ctor_set(v___x_2563_, 2, v___x_2562_);
v_toCold_2564_ = lean_ctor_get(v_a_2444_, 0);
v_cancelTk_x3f_2565_ = lean_ctor_get(v_toCold_2564_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2565_) == 1)
{
lean_object* v_val_2566_; uint8_t v___x_2567_; 
v_val_2566_ = lean_ctor_get(v_cancelTk_x3f_2565_, 0);
v___x_2567_ = l_IO_CancelToken_isSet(v_val_2566_);
if (v___x_2567_ == 0)
{
lean_dec_ref_known(v___x_2563_, 3);
goto v___jp_2495_;
}
else
{
lean_object* v___x_2058__overap_2568_; lean_object* v___x_2569_; 
v___x_2058__overap_2568_ = l_Lean_throwInterruptException___redArg(v___x_2563_);
lean_inc(v_a_2445_);
lean_inc_ref(v_a_2444_);
v___x_2569_ = lean_apply_3(v___x_2058__overap_2568_, v_a_2444_, v_a_2445_, lean_box(0));
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_dec_ref_known(v___x_2569_, 1);
goto v___jp_2495_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_a_2491_);
lean_dec_ref(v_inferType_2441_);
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2563_, 3);
goto v___jp_2495_;
}
}
}
else
{
lean_object* v_val_2579_; lean_object* v___x_2581_; 
lean_del_object(v___x_2538_);
lean_dec(v_a_2491_);
lean_dec_ref(v_inferType_2441_);
v_val_2579_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v___x_2541_, 1);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v_val_2579_);
v___x_2581_ = v___x_2493_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_val_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_inferType_2441_);
v_a_2589_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2490_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2490_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
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
else
{
lean_dec_ref(v_e_2440_);
goto v___jp_2447_;
}
}
v___jp_2447_:
{
lean_object* v___x_2448_; lean_object* v_toApplicative_2449_; lean_object* v_toFunctor_2450_; lean_object* v_toSeq_2451_; lean_object* v_toSeqLeft_2452_; lean_object* v_toSeqRight_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_toCold_2469_; lean_object* v_cancelTk_x3f_2470_; 
v___x_2448_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2449_ = lean_ctor_get(v___x_2448_, 0);
v_toFunctor_2450_ = lean_ctor_get(v_toApplicative_2449_, 0);
v_toSeq_2451_ = lean_ctor_get(v_toApplicative_2449_, 2);
v_toSeqLeft_2452_ = lean_ctor_get(v_toApplicative_2449_, 3);
v_toSeqRight_2453_ = lean_ctor_get(v_toApplicative_2449_, 4);
v___f_2454_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2455_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2450_, 2);
v___f_2456_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2456_, 0, v_toFunctor_2450_);
v___f_2457_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2457_, 0, v_toFunctor_2450_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___f_2456_);
lean_ctor_set(v___x_2458_, 1, v___f_2457_);
lean_inc(v_toSeqRight_2453_);
v___f_2459_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2459_, 0, v_toSeqRight_2453_);
lean_inc(v_toSeqLeft_2452_);
v___f_2460_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2460_, 0, v_toSeqLeft_2452_);
lean_inc(v_toSeq_2451_);
v___f_2461_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2461_, 0, v_toSeq_2451_);
v___x_2462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2458_);
lean_ctor_set(v___x_2462_, 1, v___f_2454_);
lean_ctor_set(v___x_2462_, 2, v___f_2461_);
lean_ctor_set(v___x_2462_, 3, v___f_2460_);
lean_ctor_set(v___x_2462_, 4, v___f_2459_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v___f_2455_);
v___x_2464_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2465_ = l_Lean_Core_instMonadRefCoreM;
v___x_2466_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2467_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2466_, v___x_2463_);
v___x_2468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2464_);
lean_ctor_set(v___x_2468_, 1, v___x_2465_);
lean_ctor_set(v___x_2468_, 2, v___x_2467_);
v_toCold_2469_ = lean_ctor_get(v_a_2444_, 0);
v_cancelTk_x3f_2470_ = lean_ctor_get(v_toCold_2469_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2470_) == 1)
{
lean_object* v_val_2471_; uint8_t v___x_2472_; 
v_val_2471_ = lean_ctor_get(v_cancelTk_x3f_2470_, 0);
v___x_2472_ = l_IO_CancelToken_isSet(v_val_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
lean_dec_ref_known(v___x_2468_, 3);
lean_inc(v_a_2445_);
lean_inc_ref(v_a_2444_);
lean_inc(v_a_2443_);
lean_inc_ref(v_a_2442_);
v___x_2473_ = lean_apply_5(v_inferType_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, lean_box(0));
return v___x_2473_;
}
else
{
lean_object* v___x_2031__overap_2474_; lean_object* v___x_2475_; 
v___x_2031__overap_2474_ = l_Lean_throwInterruptException___redArg(v___x_2468_);
lean_inc(v_a_2445_);
lean_inc_ref(v_a_2444_);
v___x_2475_ = lean_apply_3(v___x_2031__overap_2474_, v_a_2444_, v_a_2445_, lean_box(0));
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; 
lean_dec_ref_known(v___x_2475_, 1);
lean_inc(v_a_2445_);
lean_inc_ref(v_a_2444_);
lean_inc(v_a_2443_);
lean_inc_ref(v_a_2442_);
v___x_2476_ = lean_apply_5(v_inferType_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, lean_box(0));
return v___x_2476_;
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_inferType_2441_);
v_a_2477_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2475_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2475_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
else
{
lean_object* v___x_2485_; 
lean_dec_ref_known(v___x_2468_, 3);
lean_inc(v_a_2445_);
lean_inc_ref(v_a_2444_);
lean_inc(v_a_2443_);
lean_inc_ref(v_a_2442_);
v___x_2485_ = lean_apply_5(v_inferType_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, lean_box(0));
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2597_, lean_object* v_inferType_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2597_, v_inferType_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2657_; uint8_t v_beta_2658_; 
v___x_2657_ = l_Lean_Meta_Context_config(v___y_2606_);
v_beta_2658_ = lean_ctor_get_uint8(v___x_2657_, 13);
if (v_beta_2658_ == 0)
{
lean_dec_ref(v___x_2657_);
goto v___jp_2611_;
}
else
{
uint8_t v_iota_2659_; 
v_iota_2659_ = lean_ctor_get_uint8(v___x_2657_, 12);
if (v_iota_2659_ == 0)
{
lean_dec_ref(v___x_2657_);
goto v___jp_2611_;
}
else
{
uint8_t v_zeta_2660_; 
v_zeta_2660_ = lean_ctor_get_uint8(v___x_2657_, 15);
if (v_zeta_2660_ == 0)
{
lean_dec_ref(v___x_2657_);
goto v___jp_2611_;
}
else
{
uint8_t v_zetaHave_2661_; 
v_zetaHave_2661_ = lean_ctor_get_uint8(v___x_2657_, 18);
if (v_zetaHave_2661_ == 0)
{
lean_dec_ref(v___x_2657_);
goto v___jp_2611_;
}
else
{
uint8_t v_zetaDelta_2662_; 
v_zetaDelta_2662_ = lean_ctor_get_uint8(v___x_2657_, 16);
if (v_zetaDelta_2662_ == 0)
{
lean_dec_ref(v___x_2657_);
goto v___jp_2611_;
}
else
{
uint8_t v_etaStruct_2663_; uint8_t v_proj_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_etaStruct_2663_ = lean_ctor_get_uint8(v___x_2657_, 10);
v_proj_2664_ = lean_ctor_get_uint8(v___x_2657_, 14);
lean_dec_ref(v___x_2657_);
v___x_2665_ = lean_box(v_proj_2664_);
v___x_2666_ = lean_obj_tag_nat(v___x_2665_);
lean_dec(v___x_2665_);
v___x_2667_ = lean_unsigned_to_nat(2u);
v___x_2668_ = lean_nat_dec_eq(v___x_2666_, v___x_2667_);
if (v___x_2668_ == 0)
{
goto v___jp_2611_;
}
else
{
uint8_t v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = 0;
v___x_2670_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2663_, v___x_2669_);
if (v___x_2670_ == 0)
{
goto v___jp_2611_;
}
else
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_apply_5(v_x_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, lean_box(0));
return v___x_2671_;
}
}
}
}
}
}
}
v___jp_2611_:
{
lean_object* v___x_2612_; uint8_t v_foApprox_2613_; uint8_t v_ctxApprox_2614_; uint8_t v_quasiPatternApprox_2615_; uint8_t v_constApprox_2616_; uint8_t v_isDefEqStuckEx_2617_; uint8_t v_unificationHints_2618_; uint8_t v_proofIrrelevance_2619_; uint8_t v_assignSyntheticOpaque_2620_; uint8_t v_offsetCnstrs_2621_; uint8_t v_transparency_2622_; uint8_t v_univApprox_2623_; uint8_t v_zetaUnused_2624_; uint8_t v_canUnfoldPredicateConfig_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2656_; 
v___x_2612_ = l_Lean_Meta_Context_config(v___y_2606_);
v_foApprox_2613_ = lean_ctor_get_uint8(v___x_2612_, 0);
v_ctxApprox_2614_ = lean_ctor_get_uint8(v___x_2612_, 1);
v_quasiPatternApprox_2615_ = lean_ctor_get_uint8(v___x_2612_, 2);
v_constApprox_2616_ = lean_ctor_get_uint8(v___x_2612_, 3);
v_isDefEqStuckEx_2617_ = lean_ctor_get_uint8(v___x_2612_, 4);
v_unificationHints_2618_ = lean_ctor_get_uint8(v___x_2612_, 5);
v_proofIrrelevance_2619_ = lean_ctor_get_uint8(v___x_2612_, 6);
v_assignSyntheticOpaque_2620_ = lean_ctor_get_uint8(v___x_2612_, 7);
v_offsetCnstrs_2621_ = lean_ctor_get_uint8(v___x_2612_, 8);
v_transparency_2622_ = lean_ctor_get_uint8(v___x_2612_, 9);
v_univApprox_2623_ = lean_ctor_get_uint8(v___x_2612_, 11);
v_zetaUnused_2624_ = lean_ctor_get_uint8(v___x_2612_, 17);
v_canUnfoldPredicateConfig_2625_ = lean_ctor_get_uint8(v___x_2612_, 19);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2627_ = v___x_2612_;
v_isShared_2628_ = v_isSharedCheck_2656_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v___x_2612_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2656_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
uint8_t v___x_2629_; uint8_t v___x_2630_; uint8_t v___x_2631_; lean_object* v___x_2633_; 
v___x_2629_ = 1;
v___x_2630_ = 0;
v___x_2631_ = 2;
if (v_isShared_2628_ == 0)
{
v___x_2633_ = v___x_2627_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 0, v_foApprox_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 1, v_ctxApprox_2614_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 2, v_quasiPatternApprox_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 3, v_constApprox_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 4, v_isDefEqStuckEx_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 5, v_unificationHints_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 6, v_proofIrrelevance_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 7, v_assignSyntheticOpaque_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 8, v_offsetCnstrs_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 9, v_transparency_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 11, v_univApprox_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 17, v_zetaUnused_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, 19, v_canUnfoldPredicateConfig_2625_);
v___x_2633_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
uint8_t v_trackZetaDelta_2634_; lean_object* v_zetaDeltaSet_2635_; lean_object* v_lctx_2636_; lean_object* v_localInstances_2637_; lean_object* v_defEqCtx_x3f_2638_; lean_object* v_synthPendingDepth_2639_; lean_object* v_customCanUnfoldPredicate_x3f_2640_; uint8_t v_univApprox_2641_; uint8_t v_inTypeClassResolution_2642_; uint8_t v_cacheInferType_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2653_; 
lean_ctor_set_uint8(v___x_2633_, 10, v___x_2630_);
lean_ctor_set_uint8(v___x_2633_, 12, v___x_2629_);
lean_ctor_set_uint8(v___x_2633_, 13, v___x_2629_);
lean_ctor_set_uint8(v___x_2633_, 14, v___x_2631_);
lean_ctor_set_uint8(v___x_2633_, 15, v___x_2629_);
lean_ctor_set_uint8(v___x_2633_, 16, v___x_2629_);
lean_ctor_set_uint8(v___x_2633_, 18, v___x_2629_);
v_trackZetaDelta_2634_ = lean_ctor_get_uint8(v___y_2606_, sizeof(void*)*7);
v_zetaDeltaSet_2635_ = lean_ctor_get(v___y_2606_, 1);
v_lctx_2636_ = lean_ctor_get(v___y_2606_, 2);
v_localInstances_2637_ = lean_ctor_get(v___y_2606_, 3);
v_defEqCtx_x3f_2638_ = lean_ctor_get(v___y_2606_, 4);
v_synthPendingDepth_2639_ = lean_ctor_get(v___y_2606_, 5);
v_customCanUnfoldPredicate_x3f_2640_ = lean_ctor_get(v___y_2606_, 6);
v_univApprox_2641_ = lean_ctor_get_uint8(v___y_2606_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2642_ = lean_ctor_get_uint8(v___y_2606_, sizeof(void*)*7 + 2);
v_cacheInferType_2643_ = lean_ctor_get_uint8(v___y_2606_, sizeof(void*)*7 + 3);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___y_2606_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v___y_2606_, 0);
lean_dec(v_unused_2654_);
v___x_2645_ = v___y_2606_;
v_isShared_2646_ = v_isSharedCheck_2653_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2640_);
lean_inc(v_synthPendingDepth_2639_);
lean_inc(v_defEqCtx_x3f_2638_);
lean_inc(v_localInstances_2637_);
lean_inc(v_lctx_2636_);
lean_inc(v_zetaDeltaSet_2635_);
lean_dec(v___y_2606_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2653_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
uint64_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2647_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2633_);
v___x_2648_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2648_, 0, v___x_2633_);
lean_ctor_set_uint64(v___x_2648_, sizeof(void*)*1, v___x_2647_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2648_);
v___x_2650_ = v___x_2645_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_zetaDeltaSet_2635_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_lctx_2636_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_localInstances_2637_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_defEqCtx_x3f_2638_);
lean_ctor_set(v_reuseFailAlloc_2652_, 5, v_synthPendingDepth_2639_);
lean_ctor_set(v_reuseFailAlloc_2652_, 6, v_customCanUnfoldPredicate_x3f_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*7, v_trackZetaDelta_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*7 + 1, v_univApprox_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2652_, sizeof(void*)*7 + 3, v_cacheInferType_2643_);
v___x_2650_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_apply_5(v_x_2605_, v___x_2650_, v___y_2607_, v___y_2608_, v___y_2609_, lean_box(0));
return v___x_2651_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___y_2686_; lean_object* v___x_2703_; uint8_t v_transparency_2704_; uint8_t v___x_2705_; uint8_t v___x_2706_; 
v___x_2703_ = l_Lean_Meta_Context_config(v_a_2680_);
v_transparency_2704_ = lean_ctor_get_uint8(v___x_2703_, 9);
lean_dec_ref(v___x_2703_);
v___x_2705_ = 1;
v___x_2706_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2704_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; 
lean_inc(v_a_2683_);
lean_inc_ref(v_a_2682_);
lean_inc(v_a_2681_);
lean_inc_ref(v_a_2680_);
v___x_2707_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
v___y_2686_ = v___x_2707_;
goto v___jp_2685_;
}
else
{
lean_object* v_keyedConfig_2708_; uint8_t v_trackZetaDelta_2709_; lean_object* v_zetaDeltaSet_2710_; lean_object* v_lctx_2711_; lean_object* v_localInstances_2712_; lean_object* v_defEqCtx_x3f_2713_; lean_object* v_synthPendingDepth_2714_; lean_object* v_customCanUnfoldPredicate_x3f_2715_; uint8_t v_univApprox_2716_; uint8_t v_inTypeClassResolution_2717_; uint8_t v_cacheInferType_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_keyedConfig_2708_ = lean_ctor_get(v_a_2680_, 0);
v_trackZetaDelta_2709_ = lean_ctor_get_uint8(v_a_2680_, sizeof(void*)*7);
v_zetaDeltaSet_2710_ = lean_ctor_get(v_a_2680_, 1);
v_lctx_2711_ = lean_ctor_get(v_a_2680_, 2);
v_localInstances_2712_ = lean_ctor_get(v_a_2680_, 3);
v_defEqCtx_x3f_2713_ = lean_ctor_get(v_a_2680_, 4);
v_synthPendingDepth_2714_ = lean_ctor_get(v_a_2680_, 5);
v_customCanUnfoldPredicate_x3f_2715_ = lean_ctor_get(v_a_2680_, 6);
v_univApprox_2716_ = lean_ctor_get_uint8(v_a_2680_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2717_ = lean_ctor_get_uint8(v_a_2680_, sizeof(void*)*7 + 2);
v_cacheInferType_2718_ = lean_ctor_get_uint8(v_a_2680_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2708_);
v___x_2719_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2705_, v_keyedConfig_2708_);
lean_inc(v_customCanUnfoldPredicate_x3f_2715_);
lean_inc(v_synthPendingDepth_2714_);
lean_inc(v_defEqCtx_x3f_2713_);
lean_inc_ref(v_localInstances_2712_);
lean_inc_ref(v_lctx_2711_);
lean_inc(v_zetaDeltaSet_2710_);
v___x_2720_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v_zetaDeltaSet_2710_);
lean_ctor_set(v___x_2720_, 2, v_lctx_2711_);
lean_ctor_set(v___x_2720_, 3, v_localInstances_2712_);
lean_ctor_set(v___x_2720_, 4, v_defEqCtx_x3f_2713_);
lean_ctor_set(v___x_2720_, 5, v_synthPendingDepth_2714_);
lean_ctor_set(v___x_2720_, 6, v_customCanUnfoldPredicate_x3f_2715_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7, v_trackZetaDelta_2709_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 1, v_univApprox_2716_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2717_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 3, v_cacheInferType_2718_);
lean_inc(v_a_2683_);
lean_inc_ref(v_a_2682_);
lean_inc(v_a_2681_);
v___x_2721_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2679_, v___x_2720_, v_a_2681_, v_a_2682_, v_a_2683_);
v___y_2686_ = v___x_2721_;
goto v___jp_2685_;
}
v___jp_2685_:
{
if (lean_obj_tag(v___y_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2687_ = lean_ctor_get(v___y_2686_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___y_2686_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___y_2686_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___y_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2695_ = lean_ctor_get(v___y_2686_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___y_2686_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___y_2686_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___y_2686_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2729_, lean_object* v_x_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___y_2737_; lean_object* v___x_2754_; uint8_t v_transparency_2755_; uint8_t v___x_2756_; uint8_t v___x_2757_; 
v___x_2754_ = l_Lean_Meta_Context_config(v_a_2731_);
v_transparency_2755_ = lean_ctor_get_uint8(v___x_2754_, 9);
lean_dec_ref(v___x_2754_);
v___x_2756_ = 1;
v___x_2757_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2755_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; 
lean_inc(v_a_2734_);
lean_inc_ref(v_a_2733_);
lean_inc(v_a_2732_);
lean_inc_ref(v_a_2731_);
v___x_2758_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
v___y_2737_ = v___x_2758_;
goto v___jp_2736_;
}
else
{
lean_object* v_keyedConfig_2759_; uint8_t v_trackZetaDelta_2760_; lean_object* v_zetaDeltaSet_2761_; lean_object* v_lctx_2762_; lean_object* v_localInstances_2763_; lean_object* v_defEqCtx_x3f_2764_; lean_object* v_synthPendingDepth_2765_; lean_object* v_customCanUnfoldPredicate_x3f_2766_; uint8_t v_univApprox_2767_; uint8_t v_inTypeClassResolution_2768_; uint8_t v_cacheInferType_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_keyedConfig_2759_ = lean_ctor_get(v_a_2731_, 0);
v_trackZetaDelta_2760_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*7);
v_zetaDeltaSet_2761_ = lean_ctor_get(v_a_2731_, 1);
v_lctx_2762_ = lean_ctor_get(v_a_2731_, 2);
v_localInstances_2763_ = lean_ctor_get(v_a_2731_, 3);
v_defEqCtx_x3f_2764_ = lean_ctor_get(v_a_2731_, 4);
v_synthPendingDepth_2765_ = lean_ctor_get(v_a_2731_, 5);
v_customCanUnfoldPredicate_x3f_2766_ = lean_ctor_get(v_a_2731_, 6);
v_univApprox_2767_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2768_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*7 + 2);
v_cacheInferType_2769_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2759_);
v___x_2770_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2756_, v_keyedConfig_2759_);
lean_inc(v_customCanUnfoldPredicate_x3f_2766_);
lean_inc(v_synthPendingDepth_2765_);
lean_inc(v_defEqCtx_x3f_2764_);
lean_inc_ref(v_localInstances_2763_);
lean_inc_ref(v_lctx_2762_);
lean_inc(v_zetaDeltaSet_2761_);
v___x_2771_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set(v___x_2771_, 1, v_zetaDeltaSet_2761_);
lean_ctor_set(v___x_2771_, 2, v_lctx_2762_);
lean_ctor_set(v___x_2771_, 3, v_localInstances_2763_);
lean_ctor_set(v___x_2771_, 4, v_defEqCtx_x3f_2764_);
lean_ctor_set(v___x_2771_, 5, v_synthPendingDepth_2765_);
lean_ctor_set(v___x_2771_, 6, v_customCanUnfoldPredicate_x3f_2766_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*7, v_trackZetaDelta_2760_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*7 + 1, v_univApprox_2767_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2768_);
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*7 + 3, v_cacheInferType_2769_);
lean_inc(v_a_2734_);
lean_inc_ref(v_a_2733_);
lean_inc(v_a_2732_);
v___x_2772_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2730_, v___x_2771_, v_a_2732_, v_a_2733_, v_a_2734_);
v___y_2737_ = v___x_2772_;
goto v___jp_2736_;
}
v___jp_2736_:
{
if (lean_obj_tag(v___y_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
v_a_2738_ = lean_ctor_get(v___y_2737_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___y_2737_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___y_2737_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___y_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
v_a_2746_ = lean_ctor_get(v___y_2737_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___y_2737_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___y_2737_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___y_2737_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2773_, lean_object* v_x_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2773_, v_x_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
return v_res_2780_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_box(0);
v___x_2782_ = l_Lean_interruptExceptionId;
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2781_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v_ks_2803_; lean_object* v_vs_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2830_; 
v_ks_2803_ = lean_ctor_get(v_x_2799_, 0);
v_vs_2804_ = lean_ctor_get(v_x_2799_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2806_ = v_x_2799_;
v_isShared_2807_ = v_isSharedCheck_2830_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_vs_2804_);
lean_inc(v_ks_2803_);
lean_dec(v_x_2799_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2830_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = lean_array_get_size(v_ks_2803_);
v___x_2816_ = lean_nat_dec_lt(v_x_2800_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2806_);
lean_dec(v_x_2800_);
v___x_2817_ = lean_array_push(v_ks_2803_, v_x_2801_);
v___x_2818_ = lean_array_push(v_vs_2804_, v_x_2802_);
v___x_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
return v___x_2819_;
}
else
{
lean_object* v_expr_2820_; uint64_t v_configKey_2821_; lean_object* v_k_x27_2822_; lean_object* v_expr_2823_; uint64_t v_configKey_2824_; uint8_t v___x_2825_; 
v_expr_2820_ = lean_ctor_get(v_x_2801_, 0);
v_configKey_2821_ = lean_ctor_get_uint64(v_x_2801_, sizeof(void*)*1);
v_k_x27_2822_ = lean_array_fget_borrowed(v_ks_2803_, v_x_2800_);
v_expr_2823_ = lean_ctor_get(v_k_x27_2822_, 0);
v_configKey_2824_ = lean_ctor_get_uint64(v_k_x27_2822_, sizeof(void*)*1);
v___x_2825_ = lean_expr_equal(v_expr_2820_, v_expr_2823_);
if (v___x_2825_ == 0)
{
goto v___jp_2808_;
}
else
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_uint64_dec_eq(v_configKey_2821_, v_configKey_2824_);
if (v___x_2826_ == 0)
{
goto v___jp_2808_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_del_object(v___x_2806_);
v___x_2827_ = lean_array_fset(v_ks_2803_, v_x_2800_, v_x_2801_);
v___x_2828_ = lean_array_fset(v_vs_2804_, v_x_2800_, v_x_2802_);
lean_dec(v_x_2800_);
v___x_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
return v___x_2829_;
}
}
}
v___jp_2808_:
{
lean_object* v___x_2810_; 
if (v_isShared_2807_ == 0)
{
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_ks_2803_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_vs_2804_);
v___x_2810_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_unsigned_to_nat(1u);
v___x_2812_ = lean_nat_add(v_x_2800_, v___x_2811_);
lean_dec(v_x_2800_);
v_x_2799_ = v___x_2810_;
v_x_2800_ = v___x_2812_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2831_, lean_object* v_k_2832_, lean_object* v_v_2833_){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_unsigned_to_nat(0u);
v___x_2835_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2831_, v___x_2834_, v_k_2832_, v_v_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2836_, size_t v_x_2837_, size_t v_x_2838_, lean_object* v_x_2839_, lean_object* v_x_2840_){
_start:
{
if (lean_obj_tag(v_x_2836_) == 0)
{
lean_object* v_es_2841_; size_t v___x_2842_; size_t v___x_2843_; lean_object* v_j_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v_es_2841_ = lean_ctor_get(v_x_2836_, 0);
v___x_2842_ = ((size_t)31ULL);
v___x_2843_ = lean_usize_land(v_x_2837_, v___x_2842_);
v_j_2844_ = lean_usize_to_nat(v___x_2843_);
v___x_2845_ = lean_array_get_size(v_es_2841_);
v___x_2846_ = lean_nat_dec_lt(v_j_2844_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_dec(v_j_2844_);
lean_dec(v_x_2840_);
lean_dec_ref(v_x_2839_);
return v_x_2836_;
}
else
{
lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2891_; 
lean_inc_ref(v_es_2841_);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_x_2836_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v_x_2836_, 0);
lean_dec(v_unused_2892_);
v___x_2848_ = v_x_2836_;
v_isShared_2849_ = v_isSharedCheck_2891_;
goto v_resetjp_2847_;
}
else
{
lean_dec(v_x_2836_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2891_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v_v_2850_; lean_object* v___x_2851_; lean_object* v_xs_x27_2852_; lean_object* v___y_2854_; 
v_v_2850_ = lean_array_fget(v_es_2841_, v_j_2844_);
v___x_2851_ = lean_box(0);
v_xs_x27_2852_ = lean_array_fset(v_es_2841_, v_j_2844_, v___x_2851_);
switch(lean_obj_tag(v_v_2850_))
{
case 0:
{
lean_object* v_key_2859_; lean_object* v_val_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2876_; 
v_key_2859_ = lean_ctor_get(v_v_2850_, 0);
v_val_2860_ = lean_ctor_get(v_v_2850_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_v_2850_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2862_ = v_v_2850_;
v_isShared_2863_ = v_isSharedCheck_2876_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_val_2860_);
lean_inc(v_key_2859_);
lean_dec(v_v_2850_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2876_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v_expr_2867_; uint64_t v_configKey_2868_; lean_object* v_expr_2869_; uint64_t v_configKey_2870_; uint8_t v___x_2871_; 
v_expr_2867_ = lean_ctor_get(v_x_2839_, 0);
v_configKey_2868_ = lean_ctor_get_uint64(v_x_2839_, sizeof(void*)*1);
v_expr_2869_ = lean_ctor_get(v_key_2859_, 0);
v_configKey_2870_ = lean_ctor_get_uint64(v_key_2859_, sizeof(void*)*1);
v___x_2871_ = lean_expr_equal(v_expr_2867_, v_expr_2869_);
if (v___x_2871_ == 0)
{
lean_del_object(v___x_2862_);
goto v___jp_2864_;
}
else
{
uint8_t v___x_2872_; 
v___x_2872_ = lean_uint64_dec_eq(v_configKey_2868_, v_configKey_2870_);
if (v___x_2872_ == 0)
{
lean_del_object(v___x_2862_);
goto v___jp_2864_;
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_val_2860_);
lean_dec(v_key_2859_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 1, v_x_2840_);
lean_ctor_set(v___x_2862_, 0, v_x_2839_);
v___x_2874_ = v___x_2862_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_x_2839_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_x_2840_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
v___y_2854_ = v___x_2874_;
goto v___jp_2853_;
}
}
}
v___jp_2864_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2859_, v_val_2860_, v_x_2839_, v_x_2840_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
v___y_2854_ = v___x_2866_;
goto v___jp_2853_;
}
}
}
case 1:
{
lean_object* v_node_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2889_; 
v_node_2877_ = lean_ctor_get(v_v_2850_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_v_2850_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2879_ = v_v_2850_;
v_isShared_2880_ = v_isSharedCheck_2889_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_node_2877_);
lean_dec(v_v_2850_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2889_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
size_t v___x_2881_; size_t v___x_2882_; size_t v___x_2883_; size_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2881_ = ((size_t)5ULL);
v___x_2882_ = lean_usize_shift_right(v_x_2837_, v___x_2881_);
v___x_2883_ = ((size_t)1ULL);
v___x_2884_ = lean_usize_add(v_x_2838_, v___x_2883_);
v___x_2885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2877_, v___x_2882_, v___x_2884_, v_x_2839_, v_x_2840_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2885_);
v___x_2887_ = v___x_2879_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
v___y_2854_ = v___x_2887_;
goto v___jp_2853_;
}
}
}
default: 
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v_x_2839_);
lean_ctor_set(v___x_2890_, 1, v_x_2840_);
v___y_2854_ = v___x_2890_;
goto v___jp_2853_;
}
}
v___jp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = lean_array_fset(v_xs_x27_2852_, v_j_2844_, v___y_2854_);
lean_dec(v_j_2844_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2855_);
v___x_2857_ = v___x_2848_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
else
{
lean_object* v_ks_2893_; lean_object* v_vs_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2912_; 
v_ks_2893_ = lean_ctor_get(v_x_2836_, 0);
v_vs_2894_ = lean_ctor_get(v_x_2836_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_x_2836_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2896_ = v_x_2836_;
v_isShared_2897_ = v_isSharedCheck_2912_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_vs_2894_);
lean_inc(v_ks_2893_);
lean_dec(v_x_2836_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2912_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_ks_2893_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_vs_2894_);
v___x_2899_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v_newNode_2900_; size_t v___x_2901_; uint8_t v___x_2902_; 
v_newNode_2900_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2899_, v_x_2839_, v_x_2840_);
v___x_2901_ = ((size_t)7ULL);
v___x_2902_ = lean_usize_dec_le(v___x_2901_, v_x_2838_);
if (v___x_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2900_);
v___x_2904_ = lean_unsigned_to_nat(4u);
v___x_2905_ = lean_nat_dec_lt(v___x_2903_, v___x_2904_);
lean_dec(v___x_2903_);
if (v___x_2905_ == 0)
{
lean_object* v_ks_2906_; lean_object* v_vs_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_ks_2906_ = lean_ctor_get(v_newNode_2900_, 0);
lean_inc_ref(v_ks_2906_);
v_vs_2907_ = lean_ctor_get(v_newNode_2900_, 1);
lean_inc_ref(v_vs_2907_);
lean_dec_ref(v_newNode_2900_);
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2838_, v_ks_2906_, v_vs_2907_, v___x_2908_, v___x_2909_);
lean_dec_ref(v_vs_2907_);
lean_dec_ref(v_ks_2906_);
return v___x_2910_;
}
else
{
return v_newNode_2900_;
}
}
else
{
return v_newNode_2900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2913_, lean_object* v_keys_2914_, lean_object* v_vals_2915_, lean_object* v_i_2916_, lean_object* v_entries_2917_){
_start:
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = lean_array_get_size(v_keys_2914_);
v___x_2919_ = lean_nat_dec_lt(v_i_2916_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_dec(v_i_2916_);
return v_entries_2917_;
}
else
{
lean_object* v_k_2920_; lean_object* v_expr_2921_; uint64_t v_configKey_2922_; lean_object* v_v_2923_; uint64_t v___x_2924_; uint64_t v___x_2925_; size_t v_h_2926_; size_t v___x_2927_; lean_object* v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; size_t v_h_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_k_2920_ = lean_array_fget_borrowed(v_keys_2914_, v_i_2916_);
v_expr_2921_ = lean_ctor_get(v_k_2920_, 0);
v_configKey_2922_ = lean_ctor_get_uint64(v_k_2920_, sizeof(void*)*1);
v_v_2923_ = lean_array_fget_borrowed(v_vals_2915_, v_i_2916_);
v___x_2924_ = l_Lean_Expr_hash(v_expr_2921_);
v___x_2925_ = lean_uint64_mix_hash(v___x_2924_, v_configKey_2922_);
v_h_2926_ = lean_uint64_to_usize(v___x_2925_);
v___x_2927_ = ((size_t)5ULL);
v___x_2928_ = lean_unsigned_to_nat(1u);
v___x_2929_ = ((size_t)1ULL);
v___x_2930_ = lean_usize_sub(v_depth_2913_, v___x_2929_);
v___x_2931_ = lean_usize_mul(v___x_2927_, v___x_2930_);
v_h_2932_ = lean_usize_shift_right(v_h_2926_, v___x_2931_);
v___x_2933_ = lean_nat_add(v_i_2916_, v___x_2928_);
lean_dec(v_i_2916_);
lean_inc(v_v_2923_);
lean_inc(v_k_2920_);
v___x_2934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2917_, v_h_2932_, v_depth_2913_, v_k_2920_, v_v_2923_);
v_i_2916_ = v___x_2933_;
v_entries_2917_ = v___x_2934_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2936_, lean_object* v_keys_2937_, lean_object* v_vals_2938_, lean_object* v_i_2939_, lean_object* v_entries_2940_){
_start:
{
size_t v_depth_boxed_2941_; lean_object* v_res_2942_; 
v_depth_boxed_2941_ = lean_unbox_usize(v_depth_2936_);
lean_dec(v_depth_2936_);
v_res_2942_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2941_, v_keys_2937_, v_vals_2938_, v_i_2939_, v_entries_2940_);
lean_dec_ref(v_vals_2938_);
lean_dec_ref(v_keys_2937_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
size_t v_x_2418__boxed_2948_; size_t v_x_2419__boxed_2949_; lean_object* v_res_2950_; 
v_x_2418__boxed_2948_ = lean_unbox_usize(v_x_2944_);
lean_dec(v_x_2944_);
v_x_2419__boxed_2949_ = lean_unbox_usize(v_x_2945_);
lean_dec(v_x_2945_);
v_res_2950_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2943_, v_x_2418__boxed_2948_, v_x_2419__boxed_2949_, v_x_2946_, v_x_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2951_, lean_object* v_x_2952_, lean_object* v_x_2953_){
_start:
{
lean_object* v_expr_2954_; uint64_t v_configKey_2955_; uint64_t v___x_2956_; uint64_t v___x_2957_; size_t v___x_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v_expr_2954_ = lean_ctor_get(v_x_2952_, 0);
v_configKey_2955_ = lean_ctor_get_uint64(v_x_2952_, sizeof(void*)*1);
v___x_2956_ = l_Lean_Expr_hash(v_expr_2954_);
v___x_2957_ = lean_uint64_mix_hash(v___x_2956_, v_configKey_2955_);
v___x_2958_ = lean_uint64_to_usize(v___x_2957_);
v___x_2959_ = ((size_t)1ULL);
v___x_2960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2951_, v___x_2958_, v___x_2959_, v_x_2952_, v_x_2953_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2961_, lean_object* v_vals_2962_, lean_object* v_i_2963_, lean_object* v_k_2964_){
_start:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = lean_array_get_size(v_keys_2961_);
v___x_2970_ = lean_nat_dec_lt(v_i_2963_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
lean_dec(v_i_2963_);
v___x_2971_ = lean_box(0);
return v___x_2971_;
}
else
{
lean_object* v_expr_2972_; uint64_t v_configKey_2973_; lean_object* v_k_x27_2974_; lean_object* v_expr_2975_; uint64_t v_configKey_2976_; uint8_t v___x_2977_; 
v_expr_2972_ = lean_ctor_get(v_k_2964_, 0);
v_configKey_2973_ = lean_ctor_get_uint64(v_k_2964_, sizeof(void*)*1);
v_k_x27_2974_ = lean_array_fget_borrowed(v_keys_2961_, v_i_2963_);
v_expr_2975_ = lean_ctor_get(v_k_x27_2974_, 0);
v_configKey_2976_ = lean_ctor_get_uint64(v_k_x27_2974_, sizeof(void*)*1);
v___x_2977_ = lean_expr_equal(v_expr_2972_, v_expr_2975_);
if (v___x_2977_ == 0)
{
goto v___jp_2965_;
}
else
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_uint64_dec_eq(v_configKey_2973_, v_configKey_2976_);
if (v___x_2978_ == 0)
{
goto v___jp_2965_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_array_fget_borrowed(v_vals_2962_, v_i_2963_);
lean_dec(v_i_2963_);
lean_inc(v___x_2979_);
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
}
v___jp_2965_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_unsigned_to_nat(1u);
v___x_2967_ = lean_nat_add(v_i_2963_, v___x_2966_);
lean_dec(v_i_2963_);
v_i_2963_ = v___x_2967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_2981_, lean_object* v_vals_2982_, lean_object* v_i_2983_, lean_object* v_k_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_2981_, v_vals_2982_, v_i_2983_, v_k_2984_);
lean_dec_ref(v_k_2984_);
lean_dec_ref(v_vals_2982_);
lean_dec_ref(v_keys_2981_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_2986_, size_t v_x_2987_, lean_object* v_x_2988_){
_start:
{
if (lean_obj_tag(v_x_2986_) == 0)
{
lean_object* v_es_2989_; lean_object* v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; lean_object* v_j_2993_; lean_object* v___x_2994_; 
v_es_2989_ = lean_ctor_get(v_x_2986_, 0);
v___x_2990_ = lean_box(2);
v___x_2991_ = ((size_t)31ULL);
v___x_2992_ = lean_usize_land(v_x_2987_, v___x_2991_);
v_j_2993_ = lean_usize_to_nat(v___x_2992_);
v___x_2994_ = lean_array_get_borrowed(v___x_2990_, v_es_2989_, v_j_2993_);
lean_dec(v_j_2993_);
switch(lean_obj_tag(v___x_2994_))
{
case 0:
{
lean_object* v_key_2995_; lean_object* v_val_2996_; lean_object* v_expr_2997_; uint64_t v_configKey_2998_; lean_object* v_expr_2999_; uint64_t v_configKey_3000_; uint8_t v___x_3001_; 
v_key_2995_ = lean_ctor_get(v___x_2994_, 0);
v_val_2996_ = lean_ctor_get(v___x_2994_, 1);
v_expr_2997_ = lean_ctor_get(v_x_2988_, 0);
v_configKey_2998_ = lean_ctor_get_uint64(v_x_2988_, sizeof(void*)*1);
v_expr_2999_ = lean_ctor_get(v_key_2995_, 0);
v_configKey_3000_ = lean_ctor_get_uint64(v_key_2995_, sizeof(void*)*1);
v___x_3001_ = lean_expr_equal(v_expr_2997_, v_expr_2999_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_box(0);
return v___x_3002_;
}
else
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_uint64_dec_eq(v_configKey_2998_, v_configKey_3000_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_box(0);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; 
lean_inc(v_val_2996_);
v___x_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3005_, 0, v_val_2996_);
return v___x_3005_;
}
}
}
case 1:
{
lean_object* v_node_3006_; size_t v___x_3007_; size_t v___x_3008_; 
v_node_3006_ = lean_ctor_get(v___x_2994_, 0);
v___x_3007_ = ((size_t)5ULL);
v___x_3008_ = lean_usize_shift_right(v_x_2987_, v___x_3007_);
v_x_2986_ = v_node_3006_;
v_x_2987_ = v___x_3008_;
goto _start;
}
default: 
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_box(0);
return v___x_3010_;
}
}
}
else
{
lean_object* v_ks_3011_; lean_object* v_vs_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_ks_3011_ = lean_ctor_get(v_x_2986_, 0);
v_vs_3012_ = lean_ctor_get(v_x_2986_, 1);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3011_, v_vs_3012_, v___x_3013_, v_x_2988_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_){
_start:
{
size_t v_x_2618__boxed_3018_; lean_object* v_res_3019_; 
v_x_2618__boxed_3018_ = lean_unbox_usize(v_x_3016_);
lean_dec(v_x_3016_);
v_res_3019_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3015_, v_x_2618__boxed_3018_, v_x_3017_);
lean_dec_ref(v_x_3017_);
lean_dec_ref(v_x_3015_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
lean_object* v_expr_3022_; uint64_t v_configKey_3023_; uint64_t v___x_3024_; uint64_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v_expr_3022_ = lean_ctor_get(v_x_3021_, 0);
v_configKey_3023_ = lean_ctor_get_uint64(v_x_3021_, sizeof(void*)*1);
v___x_3024_ = l_Lean_Expr_hash(v_expr_3022_);
v___x_3025_ = lean_uint64_mix_hash(v___x_3024_, v_configKey_3023_);
v___x_3026_ = lean_uint64_to_usize(v___x_3025_);
v___x_3027_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3020_, v___x_3026_, v_x_3021_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3028_, v_x_3029_);
lean_dec_ref(v_x_3029_);
lean_dec_ref(v_x_3028_);
return v_res_3030_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3033_ = l_Lean_stringToMessageData(v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
switch(lean_obj_tag(v_e_3034_))
{
case 0:
{
lean_object* v_deBruijnIndex_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_deBruijnIndex_3072_ = lean_ctor_get(v_e_3034_, 0);
lean_inc(v_deBruijnIndex_3072_);
lean_dec_ref_known(v_e_3034_, 1);
v___x_3073_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3074_ = l_Lean_mkBVar(v_deBruijnIndex_3072_);
v___x_3075_ = l_Lean_MessageData_ofExpr(v___x_3074_);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3073_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3076_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3077_;
}
case 1:
{
lean_object* v_fvarId_3078_; lean_object* v___x_3079_; 
v_fvarId_3078_ = lean_ctor_get(v_e_3034_, 0);
lean_inc(v_fvarId_3078_);
lean_dec_ref_known(v_e_3034_, 1);
v___x_3079_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3078_, v_a_3035_, v_a_3037_, v_a_3038_);
return v___x_3079_;
}
case 2:
{
lean_object* v_mvarId_3080_; lean_object* v___x_3081_; 
v_mvarId_3080_ = lean_ctor_get(v_e_3034_, 0);
lean_inc(v_mvarId_3080_);
lean_dec_ref_known(v_e_3034_, 1);
v___x_3081_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3080_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3081_;
}
case 3:
{
lean_object* v_u_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_u_3082_ = lean_ctor_get(v_e_3034_, 0);
lean_inc(v_u_3082_);
lean_dec_ref_known(v_e_3034_, 1);
v___x_3083_ = l_Lean_Level_succ___override(v_u_3082_);
v___x_3084_ = l_Lean_mkSort(v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
case 4:
{
lean_object* v_declName_3086_; lean_object* v_us_3087_; 
v_declName_3086_ = lean_ctor_get(v_e_3034_, 0);
lean_inc(v_declName_3086_);
v_us_3087_ = lean_ctor_get(v_e_3034_, 1);
lean_inc(v_us_3087_);
if (lean_obj_tag(v_us_3087_) == 0)
{
lean_object* v___x_3104_; 
lean_dec_ref_known(v_e_3034_, 2);
v___x_3104_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3086_, v_us_3087_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3104_;
}
else
{
uint8_t v_cacheInferType_3105_; 
v_cacheInferType_3105_ = lean_ctor_get_uint8(v_a_3035_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3105_ == 0)
{
lean_dec_ref_known(v_e_3034_, 2);
goto v___jp_3088_;
}
else
{
uint8_t v___x_3106_; 
v___x_3106_ = l_Lean_Expr_hasMVar(v_e_3034_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3173_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3173_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3173_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3152_; lean_object* v_cache_3153_; lean_object* v_inferType_3154_; lean_object* v___x_3155_; 
v___x_3152_ = lean_st_ref_get(v_a_3036_);
v_cache_3153_ = lean_ctor_get(v___x_3152_, 1);
lean_inc_ref(v_cache_3153_);
lean_dec(v___x_3152_);
v_inferType_3154_ = lean_ctor_get(v_cache_3153_, 0);
lean_inc_ref(v_inferType_3154_);
lean_dec_ref(v_cache_3153_);
v___x_3155_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3154_, v_a_3108_);
lean_dec_ref(v_inferType_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_toCold_3156_; lean_object* v_cancelTk_x3f_3157_; 
lean_del_object(v___x_3110_);
v_toCold_3156_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3157_ = lean_ctor_get(v_toCold_3156_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3157_) == 1)
{
lean_object* v_val_3158_; uint8_t v___x_3159_; 
v_val_3158_ = lean_ctor_get(v_cancelTk_x3f_3157_, 0);
v___x_3159_ = l_IO_CancelToken_isSet(v_val_3158_);
if (v___x_3159_ == 0)
{
goto v___jp_3112_;
}
else
{
lean_object* v___x_3160_; lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_a_3108_);
lean_dec(v_us_3087_);
lean_dec(v_declName_3086_);
v___x_3160_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
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
else
{
goto v___jp_3112_;
}
}
else
{
lean_object* v_val_3169_; lean_object* v___x_3171_; 
lean_dec(v_a_3108_);
lean_dec(v_us_3087_);
lean_dec(v_declName_3086_);
v_val_3169_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_val_3169_);
lean_dec_ref_known(v___x_3155_, 1);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v_val_3169_);
v___x_3171_ = v___x_3110_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_val_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
v___jp_3112_:
{
lean_object* v___x_3113_; 
v___x_3113_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3086_, v_us_3087_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; uint8_t v___x_3115_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v___x_3115_ = l_Lean_Expr_hasMVar(v_a_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3150_; 
lean_inc(v_a_3114_);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v___x_3113_, 0);
lean_dec(v_unused_3151_);
v___x_3117_ = v___x_3113_;
v_isShared_3118_ = v_isSharedCheck_3150_;
goto v_resetjp_3116_;
}
else
{
lean_dec(v___x_3113_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3150_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v_cache_3120_; lean_object* v_mctx_3121_; lean_object* v_zetaDeltaFVarIds_3122_; lean_object* v_postponed_3123_; lean_object* v_diag_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3149_; 
v___x_3119_ = lean_st_ref_take(v_a_3036_);
v_cache_3120_ = lean_ctor_get(v___x_3119_, 1);
v_mctx_3121_ = lean_ctor_get(v___x_3119_, 0);
v_zetaDeltaFVarIds_3122_ = lean_ctor_get(v___x_3119_, 2);
v_postponed_3123_ = lean_ctor_get(v___x_3119_, 3);
v_diag_3124_ = lean_ctor_get(v___x_3119_, 4);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3126_ = v___x_3119_;
v_isShared_3127_ = v_isSharedCheck_3149_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_diag_3124_);
lean_inc(v_postponed_3123_);
lean_inc(v_zetaDeltaFVarIds_3122_);
lean_inc(v_cache_3120_);
lean_inc(v_mctx_3121_);
lean_dec(v___x_3119_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3149_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v_inferType_3128_; lean_object* v_funInfo_3129_; lean_object* v_synthInstance_3130_; lean_object* v_whnf_3131_; lean_object* v_defEqTrans_3132_; lean_object* v_defEqPerm_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3148_; 
v_inferType_3128_ = lean_ctor_get(v_cache_3120_, 0);
v_funInfo_3129_ = lean_ctor_get(v_cache_3120_, 1);
v_synthInstance_3130_ = lean_ctor_get(v_cache_3120_, 2);
v_whnf_3131_ = lean_ctor_get(v_cache_3120_, 3);
v_defEqTrans_3132_ = lean_ctor_get(v_cache_3120_, 4);
v_defEqPerm_3133_ = lean_ctor_get(v_cache_3120_, 5);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_cache_3120_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3135_ = v_cache_3120_;
v_isShared_3136_ = v_isSharedCheck_3148_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_defEqPerm_3133_);
lean_inc(v_defEqTrans_3132_);
lean_inc(v_whnf_3131_);
lean_inc(v_synthInstance_3130_);
lean_inc(v_funInfo_3129_);
lean_inc(v_inferType_3128_);
lean_dec(v_cache_3120_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3148_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_inc(v_a_3114_);
v___x_3137_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3128_, v_a_3108_, v_a_3114_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3139_ = v___x_3135_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_funInfo_3129_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_synthInstance_3130_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_whnf_3131_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_defEqTrans_3132_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v_defEqPerm_3133_);
v___x_3139_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3141_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 1, v___x_3139_);
v___x_3141_ = v___x_3126_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_mctx_3121_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_zetaDeltaFVarIds_3122_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_postponed_3123_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v_diag_3124_);
v___x_3141_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_st_ref_put(v_a_3036_, v___x_3141_);
if (v_isShared_3118_ == 0)
{
v___x_3144_ = v___x_3117_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3114_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3108_);
return v___x_3113_;
}
}
else
{
lean_dec(v_a_3108_);
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v_us_3087_);
lean_dec(v_declName_3086_);
v_a_3174_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3107_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3107_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3034_, 2);
goto v___jp_3088_;
}
}
}
v___jp_3088_:
{
lean_object* v_toCold_3089_; lean_object* v_cancelTk_x3f_3090_; 
v_toCold_3089_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3090_ = lean_ctor_get(v_toCold_3089_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3090_) == 1)
{
lean_object* v_val_3091_; uint8_t v___x_3092_; 
v_val_3091_ = lean_ctor_get(v_cancelTk_x3f_3090_, 0);
v___x_3092_ = l_IO_CancelToken_isSet(v_val_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; 
v___x_3093_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3086_, v_us_3087_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3093_;
}
else
{
lean_object* v___x_3094_; lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_us_3087_);
lean_dec(v_declName_3086_);
v___x_3094_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v___x_3103_; 
v___x_3103_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3086_, v_us_3087_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3103_;
}
}
}
case 5:
{
lean_object* v_fn_3182_; uint8_t v_cacheInferType_3183_; lean_object* v_nargs_3184_; lean_object* v___x_3185_; lean_object* v_dummy_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_fn_3182_ = lean_ctor_get(v_e_3034_, 0);
v_cacheInferType_3183_ = lean_ctor_get_uint8(v_a_3035_, sizeof(void*)*7 + 3);
v_nargs_3184_ = l_Lean_Expr_getAppNumArgs(v_e_3034_);
v___x_3185_ = l_Lean_Expr_getAppFn(v_fn_3182_);
v_dummy_3186_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3184_);
v___x_3187_ = lean_mk_array(v_nargs_3184_, v_dummy_3186_);
v___x_3188_ = lean_unsigned_to_nat(1u);
v___x_3189_ = lean_nat_sub(v_nargs_3184_, v___x_3188_);
lean_dec(v_nargs_3184_);
lean_inc_ref(v_e_3034_);
v___x_3190_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3034_, v___x_3187_, v___x_3189_);
if (v_cacheInferType_3183_ == 0)
{
lean_dec_ref_known(v_e_3034_, 2);
goto v___jp_3191_;
}
else
{
uint8_t v___x_3207_; 
v___x_3207_ = l_Lean_Expr_hasMVar(v_e_3034_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3274_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3274_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3274_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3253_; lean_object* v_cache_3254_; lean_object* v_inferType_3255_; lean_object* v___x_3256_; 
v___x_3253_ = lean_st_ref_get(v_a_3036_);
v_cache_3254_ = lean_ctor_get(v___x_3253_, 1);
lean_inc_ref(v_cache_3254_);
lean_dec(v___x_3253_);
v_inferType_3255_ = lean_ctor_get(v_cache_3254_, 0);
lean_inc_ref(v_inferType_3255_);
lean_dec_ref(v_cache_3254_);
v___x_3256_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3255_, v_a_3209_);
lean_dec_ref(v_inferType_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_toCold_3257_; lean_object* v_cancelTk_x3f_3258_; 
lean_del_object(v___x_3211_);
v_toCold_3257_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3258_ = lean_ctor_get(v_toCold_3257_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3258_) == 1)
{
lean_object* v_val_3259_; uint8_t v___x_3260_; 
v_val_3259_ = lean_ctor_get(v_cancelTk_x3f_3258_, 0);
v___x_3260_ = l_IO_CancelToken_isSet(v_val_3259_);
if (v___x_3260_ == 0)
{
goto v___jp_3213_;
}
else
{
lean_object* v___x_3261_; lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_a_3209_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v___x_3185_);
v___x_3261_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
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
else
{
goto v___jp_3213_;
}
}
else
{
lean_object* v_val_3270_; lean_object* v___x_3272_; 
lean_dec(v_a_3209_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v___x_3185_);
v_val_3270_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v___x_3256_, 1);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v_val_3270_);
v___x_3272_ = v___x_3211_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_val_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
v___jp_3213_:
{
lean_object* v___x_3214_; 
v___x_3214_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3185_, v___x_3190_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec_ref(v___x_3190_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; uint8_t v___x_3216_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v___x_3216_ = l_Lean_Expr_hasMVar(v_a_3215_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3251_; 
lean_inc(v_a_3215_);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3214_, 0);
lean_dec(v_unused_3252_);
v___x_3218_ = v___x_3214_;
v_isShared_3219_ = v_isSharedCheck_3251_;
goto v_resetjp_3217_;
}
else
{
lean_dec(v___x_3214_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3251_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v_cache_3221_; lean_object* v_mctx_3222_; lean_object* v_zetaDeltaFVarIds_3223_; lean_object* v_postponed_3224_; lean_object* v_diag_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3250_; 
v___x_3220_ = lean_st_ref_take(v_a_3036_);
v_cache_3221_ = lean_ctor_get(v___x_3220_, 1);
v_mctx_3222_ = lean_ctor_get(v___x_3220_, 0);
v_zetaDeltaFVarIds_3223_ = lean_ctor_get(v___x_3220_, 2);
v_postponed_3224_ = lean_ctor_get(v___x_3220_, 3);
v_diag_3225_ = lean_ctor_get(v___x_3220_, 4);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3227_ = v___x_3220_;
v_isShared_3228_ = v_isSharedCheck_3250_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_diag_3225_);
lean_inc(v_postponed_3224_);
lean_inc(v_zetaDeltaFVarIds_3223_);
lean_inc(v_cache_3221_);
lean_inc(v_mctx_3222_);
lean_dec(v___x_3220_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3250_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_inferType_3229_; lean_object* v_funInfo_3230_; lean_object* v_synthInstance_3231_; lean_object* v_whnf_3232_; lean_object* v_defEqTrans_3233_; lean_object* v_defEqPerm_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3249_; 
v_inferType_3229_ = lean_ctor_get(v_cache_3221_, 0);
v_funInfo_3230_ = lean_ctor_get(v_cache_3221_, 1);
v_synthInstance_3231_ = lean_ctor_get(v_cache_3221_, 2);
v_whnf_3232_ = lean_ctor_get(v_cache_3221_, 3);
v_defEqTrans_3233_ = lean_ctor_get(v_cache_3221_, 4);
v_defEqPerm_3234_ = lean_ctor_get(v_cache_3221_, 5);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_cache_3221_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3236_ = v_cache_3221_;
v_isShared_3237_ = v_isSharedCheck_3249_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_defEqPerm_3234_);
lean_inc(v_defEqTrans_3233_);
lean_inc(v_whnf_3232_);
lean_inc(v_synthInstance_3231_);
lean_inc(v_funInfo_3230_);
lean_inc(v_inferType_3229_);
lean_dec(v_cache_3221_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3249_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_inc(v_a_3215_);
v___x_3238_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3229_, v_a_3209_, v_a_3215_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3238_);
v___x_3240_ = v___x_3236_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_funInfo_3230_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_synthInstance_3231_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v_whnf_3232_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v_defEqTrans_3233_);
lean_ctor_set(v_reuseFailAlloc_3248_, 5, v_defEqPerm_3234_);
v___x_3240_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3242_; 
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 1, v___x_3240_);
v___x_3242_ = v___x_3227_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_mctx_3222_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_zetaDeltaFVarIds_3223_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_postponed_3224_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_diag_3225_);
v___x_3242_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = lean_st_ref_put(v_a_3036_, v___x_3242_);
if (v_isShared_3219_ == 0)
{
v___x_3245_ = v___x_3218_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3215_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3209_);
return v___x_3214_;
}
}
else
{
lean_dec(v_a_3209_);
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec_ref(v___x_3190_);
lean_dec_ref(v___x_3185_);
v_a_3275_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3208_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3208_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3034_, 2);
goto v___jp_3191_;
}
}
v___jp_3191_:
{
lean_object* v_toCold_3192_; lean_object* v_cancelTk_x3f_3193_; 
v_toCold_3192_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3193_ = lean_ctor_get(v_toCold_3192_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3193_) == 1)
{
lean_object* v_val_3194_; uint8_t v___x_3195_; 
v_val_3194_ = lean_ctor_get(v_cancelTk_x3f_3193_, 0);
v___x_3195_ = l_IO_CancelToken_isSet(v_val_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3185_, v___x_3190_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec_ref(v___x_3190_);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v___x_3190_);
lean_dec_ref(v___x_3185_);
v___x_3197_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v___x_3206_; 
v___x_3206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3185_, v___x_3190_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec_ref(v___x_3190_);
return v___x_3206_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3283_; 
v_cacheInferType_3283_ = lean_ctor_get_uint8(v_a_3035_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3283_ == 0)
{
goto v___jp_3056_;
}
else
{
uint8_t v___x_3284_; 
v___x_3284_ = l_Lean_Expr_hasMVar(v_e_3034_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; 
lean_inc_ref(v_e_3034_);
v___x_3285_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3351_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3351_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3351_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3330_; lean_object* v_cache_3331_; lean_object* v_inferType_3332_; lean_object* v___x_3333_; 
v___x_3330_ = lean_st_ref_get(v_a_3036_);
v_cache_3331_ = lean_ctor_get(v___x_3330_, 1);
lean_inc_ref(v_cache_3331_);
lean_dec(v___x_3330_);
v_inferType_3332_ = lean_ctor_get(v_cache_3331_, 0);
lean_inc_ref(v_inferType_3332_);
lean_dec_ref(v_cache_3331_);
v___x_3333_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3332_, v_a_3286_);
lean_dec_ref(v_inferType_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_toCold_3334_; lean_object* v_cancelTk_x3f_3335_; 
lean_del_object(v___x_3288_);
v_toCold_3334_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3335_ = lean_ctor_get(v_toCold_3334_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3335_) == 1)
{
lean_object* v_val_3336_; uint8_t v___x_3337_; 
v_val_3336_ = lean_ctor_get(v_cancelTk_x3f_3335_, 0);
v___x_3337_ = l_IO_CancelToken_isSet(v_val_3336_);
if (v___x_3337_ == 0)
{
goto v___jp_3290_;
}
else
{
lean_object* v___x_3338_; lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec(v_a_3286_);
lean_dec_ref_known(v_e_3034_, 3);
v___x_3338_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
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
else
{
goto v___jp_3290_;
}
}
else
{
lean_object* v_val_3347_; lean_object* v___x_3349_; 
lean_dec(v_a_3286_);
lean_dec_ref_known(v_e_3034_, 3);
v_val_3347_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v___x_3333_, 1);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v_val_3347_);
v___x_3349_ = v___x_3288_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_val_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
v___jp_3290_:
{
lean_object* v___x_3291_; 
v___x_3291_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; uint8_t v___x_3293_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v___x_3293_ = l_Lean_Expr_hasMVar(v_a_3292_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3328_; 
lean_inc(v_a_3292_);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v___x_3291_, 0);
lean_dec(v_unused_3329_);
v___x_3295_ = v___x_3291_;
v_isShared_3296_ = v_isSharedCheck_3328_;
goto v_resetjp_3294_;
}
else
{
lean_dec(v___x_3291_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3328_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v_cache_3298_; lean_object* v_mctx_3299_; lean_object* v_zetaDeltaFVarIds_3300_; lean_object* v_postponed_3301_; lean_object* v_diag_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3327_; 
v___x_3297_ = lean_st_ref_take(v_a_3036_);
v_cache_3298_ = lean_ctor_get(v___x_3297_, 1);
v_mctx_3299_ = lean_ctor_get(v___x_3297_, 0);
v_zetaDeltaFVarIds_3300_ = lean_ctor_get(v___x_3297_, 2);
v_postponed_3301_ = lean_ctor_get(v___x_3297_, 3);
v_diag_3302_ = lean_ctor_get(v___x_3297_, 4);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3304_ = v___x_3297_;
v_isShared_3305_ = v_isSharedCheck_3327_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_diag_3302_);
lean_inc(v_postponed_3301_);
lean_inc(v_zetaDeltaFVarIds_3300_);
lean_inc(v_cache_3298_);
lean_inc(v_mctx_3299_);
lean_dec(v___x_3297_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3327_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_inferType_3306_; lean_object* v_funInfo_3307_; lean_object* v_synthInstance_3308_; lean_object* v_whnf_3309_; lean_object* v_defEqTrans_3310_; lean_object* v_defEqPerm_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3326_; 
v_inferType_3306_ = lean_ctor_get(v_cache_3298_, 0);
v_funInfo_3307_ = lean_ctor_get(v_cache_3298_, 1);
v_synthInstance_3308_ = lean_ctor_get(v_cache_3298_, 2);
v_whnf_3309_ = lean_ctor_get(v_cache_3298_, 3);
v_defEqTrans_3310_ = lean_ctor_get(v_cache_3298_, 4);
v_defEqPerm_3311_ = lean_ctor_get(v_cache_3298_, 5);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_cache_3298_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3313_ = v_cache_3298_;
v_isShared_3314_ = v_isSharedCheck_3326_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_defEqPerm_3311_);
lean_inc(v_defEqTrans_3310_);
lean_inc(v_whnf_3309_);
lean_inc(v_synthInstance_3308_);
lean_inc(v_funInfo_3307_);
lean_inc(v_inferType_3306_);
lean_dec(v_cache_3298_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3326_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
lean_inc(v_a_3292_);
v___x_3315_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3306_, v_a_3286_, v_a_3292_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 0, v___x_3315_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_funInfo_3307_);
lean_ctor_set(v_reuseFailAlloc_3325_, 2, v_synthInstance_3308_);
lean_ctor_set(v_reuseFailAlloc_3325_, 3, v_whnf_3309_);
lean_ctor_set(v_reuseFailAlloc_3325_, 4, v_defEqTrans_3310_);
lean_ctor_set(v_reuseFailAlloc_3325_, 5, v_defEqPerm_3311_);
v___x_3317_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3319_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v___x_3317_);
v___x_3319_ = v___x_3304_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_mctx_3299_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_zetaDeltaFVarIds_3300_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v_postponed_3301_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v_diag_3302_);
v___x_3319_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3322_; 
v___x_3320_ = lean_st_ref_put(v_a_3036_, v___x_3319_);
if (v_isShared_3296_ == 0)
{
v___x_3322_ = v___x_3295_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3292_);
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
}
}
}
else
{
lean_dec(v_a_3286_);
return v___x_3291_;
}
}
else
{
lean_dec(v_a_3286_);
return v___x_3291_;
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref_known(v_e_3034_, 3);
v_a_3352_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3285_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3285_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
goto v___jp_3056_;
}
}
}
case 9:
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_a_3360_ = lean_ctor_get(v_e_3034_, 0);
lean_inc_ref(v_a_3360_);
lean_dec_ref_known(v_e_3034_, 1);
v___x_3361_ = l_Lean_Literal_type(v_a_3360_);
lean_dec_ref(v_a_3360_);
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
return v___x_3362_;
}
case 10:
{
lean_object* v_expr_3363_; 
v_expr_3363_ = lean_ctor_get(v_e_3034_, 1);
lean_inc_ref(v_expr_3363_);
lean_dec_ref_known(v_e_3034_, 2);
v_e_3034_ = v_expr_3363_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3365_; lean_object* v_idx_3366_; lean_object* v_struct_3367_; uint8_t v_cacheInferType_3384_; 
v_typeName_3365_ = lean_ctor_get(v_e_3034_, 0);
lean_inc(v_typeName_3365_);
v_idx_3366_ = lean_ctor_get(v_e_3034_, 1);
lean_inc(v_idx_3366_);
v_struct_3367_ = lean_ctor_get(v_e_3034_, 2);
lean_inc_ref(v_struct_3367_);
v_cacheInferType_3384_ = lean_ctor_get_uint8(v_a_3035_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3384_ == 0)
{
lean_dec_ref_known(v_e_3034_, 3);
goto v___jp_3368_;
}
else
{
uint8_t v___x_3385_; 
v___x_3385_ = l_Lean_Expr_hasMVar(v_e_3034_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3452_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3452_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3452_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3431_; lean_object* v_cache_3432_; lean_object* v_inferType_3433_; lean_object* v___x_3434_; 
v___x_3431_ = lean_st_ref_get(v_a_3036_);
v_cache_3432_ = lean_ctor_get(v___x_3431_, 1);
lean_inc_ref(v_cache_3432_);
lean_dec(v___x_3431_);
v_inferType_3433_ = lean_ctor_get(v_cache_3432_, 0);
lean_inc_ref(v_inferType_3433_);
lean_dec_ref(v_cache_3432_);
v___x_3434_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3433_, v_a_3387_);
lean_dec_ref(v_inferType_3433_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_toCold_3435_; lean_object* v_cancelTk_x3f_3436_; 
lean_del_object(v___x_3389_);
v_toCold_3435_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3436_ = lean_ctor_get(v_toCold_3435_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3436_) == 1)
{
lean_object* v_val_3437_; uint8_t v___x_3438_; 
v_val_3437_ = lean_ctor_get(v_cancelTk_x3f_3436_, 0);
v___x_3438_ = l_IO_CancelToken_isSet(v_val_3437_);
if (v___x_3438_ == 0)
{
goto v___jp_3391_;
}
else
{
lean_object* v___x_3439_; lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_a_3387_);
lean_dec_ref(v_struct_3367_);
lean_dec(v_idx_3366_);
lean_dec(v_typeName_3365_);
v___x_3439_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
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
else
{
goto v___jp_3391_;
}
}
else
{
lean_object* v_val_3448_; lean_object* v___x_3450_; 
lean_dec(v_a_3387_);
lean_dec_ref(v_struct_3367_);
lean_dec(v_idx_3366_);
lean_dec(v_typeName_3365_);
v_val_3448_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v___x_3434_, 1);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v_val_3448_);
v___x_3450_ = v___x_3389_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_val_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
v___jp_3391_:
{
lean_object* v___x_3392_; 
v___x_3392_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3365_, v_idx_3366_, v_struct_3367_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; uint8_t v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v___x_3394_ = l_Lean_Expr_hasMVar(v_a_3393_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3429_; 
lean_inc(v_a_3393_);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v___x_3392_, 0);
lean_dec(v_unused_3430_);
v___x_3396_ = v___x_3392_;
v_isShared_3397_ = v_isSharedCheck_3429_;
goto v_resetjp_3395_;
}
else
{
lean_dec(v___x_3392_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3429_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v_cache_3399_; lean_object* v_mctx_3400_; lean_object* v_zetaDeltaFVarIds_3401_; lean_object* v_postponed_3402_; lean_object* v_diag_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3428_; 
v___x_3398_ = lean_st_ref_take(v_a_3036_);
v_cache_3399_ = lean_ctor_get(v___x_3398_, 1);
v_mctx_3400_ = lean_ctor_get(v___x_3398_, 0);
v_zetaDeltaFVarIds_3401_ = lean_ctor_get(v___x_3398_, 2);
v_postponed_3402_ = lean_ctor_get(v___x_3398_, 3);
v_diag_3403_ = lean_ctor_get(v___x_3398_, 4);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3405_ = v___x_3398_;
v_isShared_3406_ = v_isSharedCheck_3428_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_diag_3403_);
lean_inc(v_postponed_3402_);
lean_inc(v_zetaDeltaFVarIds_3401_);
lean_inc(v_cache_3399_);
lean_inc(v_mctx_3400_);
lean_dec(v___x_3398_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3428_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_inferType_3407_; lean_object* v_funInfo_3408_; lean_object* v_synthInstance_3409_; lean_object* v_whnf_3410_; lean_object* v_defEqTrans_3411_; lean_object* v_defEqPerm_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3427_; 
v_inferType_3407_ = lean_ctor_get(v_cache_3399_, 0);
v_funInfo_3408_ = lean_ctor_get(v_cache_3399_, 1);
v_synthInstance_3409_ = lean_ctor_get(v_cache_3399_, 2);
v_whnf_3410_ = lean_ctor_get(v_cache_3399_, 3);
v_defEqTrans_3411_ = lean_ctor_get(v_cache_3399_, 4);
v_defEqPerm_3412_ = lean_ctor_get(v_cache_3399_, 5);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_cache_3399_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3414_ = v_cache_3399_;
v_isShared_3415_ = v_isSharedCheck_3427_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_defEqPerm_3412_);
lean_inc(v_defEqTrans_3411_);
lean_inc(v_whnf_3410_);
lean_inc(v_synthInstance_3409_);
lean_inc(v_funInfo_3408_);
lean_inc(v_inferType_3407_);
lean_dec(v_cache_3399_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3427_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
lean_inc(v_a_3393_);
v___x_3416_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3407_, v_a_3387_, v_a_3393_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_funInfo_3408_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_synthInstance_3409_);
lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_whnf_3410_);
lean_ctor_set(v_reuseFailAlloc_3426_, 4, v_defEqTrans_3411_);
lean_ctor_set(v_reuseFailAlloc_3426_, 5, v_defEqPerm_3412_);
v___x_3418_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3418_);
v___x_3420_ = v___x_3405_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_mctx_3400_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_zetaDeltaFVarIds_3401_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_postponed_3402_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_diag_3403_);
v___x_3420_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3421_ = lean_st_ref_put(v_a_3036_, v___x_3420_);
if (v_isShared_3397_ == 0)
{
v___x_3423_ = v___x_3396_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3393_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3387_);
return v___x_3392_;
}
}
else
{
lean_dec(v_a_3387_);
return v___x_3392_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v_struct_3367_);
lean_dec(v_idx_3366_);
lean_dec(v_typeName_3365_);
v_a_3453_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3386_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3386_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3034_, 3);
goto v___jp_3368_;
}
}
v___jp_3368_:
{
lean_object* v_toCold_3369_; lean_object* v_cancelTk_x3f_3370_; 
v_toCold_3369_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3370_ = lean_ctor_get(v_toCold_3369_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3370_) == 1)
{
lean_object* v_val_3371_; uint8_t v___x_3372_; 
v_val_3371_ = lean_ctor_get(v_cancelTk_x3f_3370_, 0);
v___x_3372_ = l_IO_CancelToken_isSet(v_val_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; 
v___x_3373_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3365_, v_idx_3366_, v_struct_3367_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3373_;
}
else
{
lean_object* v___x_3374_; lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v_struct_3367_);
lean_dec(v_idx_3366_);
lean_dec(v_typeName_3365_);
v___x_3374_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
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
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3365_, v_idx_3366_, v_struct_3367_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3383_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3461_; 
v_cacheInferType_3461_ = lean_ctor_get_uint8(v_a_3035_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3461_ == 0)
{
goto v___jp_3040_;
}
else
{
uint8_t v___x_3462_; 
v___x_3462_ = l_Lean_Expr_hasMVar(v_e_3034_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_inc_ref(v_e_3034_);
v___x_3463_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3034_, v_a_3035_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3529_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3529_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3529_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3508_; lean_object* v_cache_3509_; lean_object* v_inferType_3510_; lean_object* v___x_3511_; 
v___x_3508_ = lean_st_ref_get(v_a_3036_);
v_cache_3509_ = lean_ctor_get(v___x_3508_, 1);
lean_inc_ref(v_cache_3509_);
lean_dec(v___x_3508_);
v_inferType_3510_ = lean_ctor_get(v_cache_3509_, 0);
lean_inc_ref(v_inferType_3510_);
lean_dec_ref(v_cache_3509_);
v___x_3511_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3510_, v_a_3464_);
lean_dec_ref(v_inferType_3510_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_toCold_3512_; lean_object* v_cancelTk_x3f_3513_; 
lean_del_object(v___x_3466_);
v_toCold_3512_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3513_ = lean_ctor_get(v_toCold_3512_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3513_) == 1)
{
lean_object* v_val_3514_; uint8_t v___x_3515_; 
v_val_3514_ = lean_ctor_get(v_cancelTk_x3f_3513_, 0);
v___x_3515_ = l_IO_CancelToken_isSet(v_val_3514_);
if (v___x_3515_ == 0)
{
goto v___jp_3468_;
}
else
{
lean_object* v___x_3516_; lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v_a_3464_);
lean_dec_ref(v_e_3034_);
v___x_3516_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
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
else
{
goto v___jp_3468_;
}
}
else
{
lean_object* v_val_3525_; lean_object* v___x_3527_; 
lean_dec(v_a_3464_);
lean_dec_ref(v_e_3034_);
v_val_3525_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v___x_3511_, 1);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v_val_3525_);
v___x_3527_ = v___x_3466_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_val_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
v___jp_3468_:
{
lean_object* v___x_3469_; 
v___x_3469_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; uint8_t v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
v___x_3471_ = l_Lean_Expr_hasMVar(v_a_3470_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3506_; 
lean_inc(v_a_3470_);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v___x_3469_, 0);
lean_dec(v_unused_3507_);
v___x_3473_ = v___x_3469_;
v_isShared_3474_ = v_isSharedCheck_3506_;
goto v_resetjp_3472_;
}
else
{
lean_dec(v___x_3469_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3506_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v_cache_3476_; lean_object* v_mctx_3477_; lean_object* v_zetaDeltaFVarIds_3478_; lean_object* v_postponed_3479_; lean_object* v_diag_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3505_; 
v___x_3475_ = lean_st_ref_take(v_a_3036_);
v_cache_3476_ = lean_ctor_get(v___x_3475_, 1);
v_mctx_3477_ = lean_ctor_get(v___x_3475_, 0);
v_zetaDeltaFVarIds_3478_ = lean_ctor_get(v___x_3475_, 2);
v_postponed_3479_ = lean_ctor_get(v___x_3475_, 3);
v_diag_3480_ = lean_ctor_get(v___x_3475_, 4);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3482_ = v___x_3475_;
v_isShared_3483_ = v_isSharedCheck_3505_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_diag_3480_);
lean_inc(v_postponed_3479_);
lean_inc(v_zetaDeltaFVarIds_3478_);
lean_inc(v_cache_3476_);
lean_inc(v_mctx_3477_);
lean_dec(v___x_3475_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3505_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_inferType_3484_; lean_object* v_funInfo_3485_; lean_object* v_synthInstance_3486_; lean_object* v_whnf_3487_; lean_object* v_defEqTrans_3488_; lean_object* v_defEqPerm_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3504_; 
v_inferType_3484_ = lean_ctor_get(v_cache_3476_, 0);
v_funInfo_3485_ = lean_ctor_get(v_cache_3476_, 1);
v_synthInstance_3486_ = lean_ctor_get(v_cache_3476_, 2);
v_whnf_3487_ = lean_ctor_get(v_cache_3476_, 3);
v_defEqTrans_3488_ = lean_ctor_get(v_cache_3476_, 4);
v_defEqPerm_3489_ = lean_ctor_get(v_cache_3476_, 5);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_cache_3476_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3491_ = v_cache_3476_;
v_isShared_3492_ = v_isSharedCheck_3504_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_defEqPerm_3489_);
lean_inc(v_defEqTrans_3488_);
lean_inc(v_whnf_3487_);
lean_inc(v_synthInstance_3486_);
lean_inc(v_funInfo_3485_);
lean_inc(v_inferType_3484_);
lean_dec(v_cache_3476_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3504_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_inc(v_a_3470_);
v___x_3493_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3484_, v_a_3464_, v_a_3470_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3493_);
v___x_3495_ = v___x_3491_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_funInfo_3485_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_synthInstance_3486_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_whnf_3487_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_defEqTrans_3488_);
lean_ctor_set(v_reuseFailAlloc_3503_, 5, v_defEqPerm_3489_);
v___x_3495_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v___x_3495_);
v___x_3497_ = v___x_3482_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_mctx_3477_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_zetaDeltaFVarIds_3478_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_postponed_3479_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v_diag_3480_);
v___x_3497_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = lean_st_ref_put(v_a_3036_, v___x_3497_);
if (v_isShared_3474_ == 0)
{
v___x_3500_ = v___x_3473_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3470_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3464_);
return v___x_3469_;
}
}
else
{
lean_dec(v_a_3464_);
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec_ref(v_e_3034_);
v_a_3530_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3463_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3463_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
goto v___jp_3040_;
}
}
}
}
v___jp_3040_:
{
lean_object* v_toCold_3041_; lean_object* v_cancelTk_x3f_3042_; 
v_toCold_3041_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3042_ = lean_ctor_get(v_toCold_3041_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3042_) == 1)
{
lean_object* v_val_3043_; uint8_t v___x_3044_; 
v_val_3043_ = lean_ctor_get(v_cancelTk_x3f_3042_, 0);
v___x_3044_ = l_IO_CancelToken_isSet(v_val_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
v___x_3045_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v_e_3034_);
v___x_3046_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3055_;
}
}
v___jp_3056_:
{
lean_object* v_toCold_3057_; lean_object* v_cancelTk_x3f_3058_; 
v_toCold_3057_ = lean_ctor_get(v_a_3037_, 0);
v_cancelTk_x3f_3058_ = lean_ctor_get(v_toCold_3057_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3058_) == 1)
{
lean_object* v_val_3059_; uint8_t v___x_3060_; 
v_val_3059_ = lean_ctor_get(v_cancelTk_x3f_3058_, 0);
v___x_3060_ = l_IO_CancelToken_isSet(v_val_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; 
v___x_3061_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3061_;
}
else
{
lean_object* v___x_3062_; lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec_ref(v_e_3034_);
v___x_3062_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3062_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3062_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_, lean_object* v_x_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3546_, v_x_3547_, v_x_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3551_, v_x_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3554_, lean_object* v_x_3555_, lean_object* v_x_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3554_, v_x_3555_, v_x_3556_);
lean_dec_ref(v_x_3556_);
lean_dec_ref(v_x_3555_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3558_, lean_object* v_x_3559_, size_t v_x_3560_, size_t v_x_3561_, lean_object* v_x_3562_, lean_object* v_x_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3559_, v_x_3560_, v_x_3561_, v_x_3562_, v_x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3565_, lean_object* v_x_3566_, lean_object* v_x_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_){
_start:
{
size_t v_x_3654__boxed_3571_; size_t v_x_3655__boxed_3572_; lean_object* v_res_3573_; 
v_x_3654__boxed_3571_ = lean_unbox_usize(v_x_3567_);
lean_dec(v_x_3567_);
v_x_3655__boxed_3572_ = lean_unbox_usize(v_x_3568_);
lean_dec(v_x_3568_);
v_res_3573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3565_, v_x_3566_, v_x_3654__boxed_3571_, v_x_3655__boxed_3572_, v_x_3569_, v_x_3570_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3574_, lean_object* v_x_3575_, size_t v_x_3576_, lean_object* v_x_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3575_, v_x_3576_, v_x_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_){
_start:
{
size_t v_x_3671__boxed_3583_; lean_object* v_res_3584_; 
v_x_3671__boxed_3583_ = lean_unbox_usize(v_x_3581_);
lean_dec(v_x_3581_);
v_res_3584_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3579_, v_x_3580_, v_x_3671__boxed_3583_, v_x_3582_);
lean_dec_ref(v_x_3582_);
lean_dec_ref(v_x_3580_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3585_, lean_object* v_n_3586_, lean_object* v_k_3587_, lean_object* v_v_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3586_, v_k_3587_, v_v_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3590_, size_t v_depth_3591_, lean_object* v_keys_3592_, lean_object* v_vals_3593_, lean_object* v_heq_3594_, lean_object* v_i_3595_, lean_object* v_entries_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3591_, v_keys_3592_, v_vals_3593_, v_i_3595_, v_entries_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3598_, lean_object* v_depth_3599_, lean_object* v_keys_3600_, lean_object* v_vals_3601_, lean_object* v_heq_3602_, lean_object* v_i_3603_, lean_object* v_entries_3604_){
_start:
{
size_t v_depth_boxed_3605_; lean_object* v_res_3606_; 
v_depth_boxed_3605_ = lean_unbox_usize(v_depth_3599_);
lean_dec(v_depth_3599_);
v_res_3606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3598_, v_depth_boxed_3605_, v_keys_3600_, v_vals_3601_, v_heq_3602_, v_i_3603_, v_entries_3604_);
lean_dec_ref(v_vals_3601_);
lean_dec_ref(v_keys_3600_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3607_, lean_object* v_keys_3608_, lean_object* v_vals_3609_, lean_object* v_heq_3610_, lean_object* v_i_3611_, lean_object* v_k_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3608_, v_vals_3609_, v_i_3611_, v_k_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3614_, lean_object* v_keys_3615_, lean_object* v_vals_3616_, lean_object* v_heq_3617_, lean_object* v_i_3618_, lean_object* v_k_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3614_, v_keys_3615_, v_vals_3616_, v_heq_3617_, v_i_3618_, v_k_3619_);
lean_dec_ref(v_k_3619_);
lean_dec_ref(v_vals_3616_);
lean_dec_ref(v_keys_3615_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3622_, v_x_3623_, v_x_3624_, v_x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = l_Lean_maxRecDepthErrorMessage;
v___x_3633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3635_ = l_Lean_MessageData_ofFormat(v___x_3634_);
return v___x_3635_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3637_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3638_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
lean_ctor_set(v___x_3638_, 1, v___x_3636_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3639_){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v_ref_3639_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3644_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3647_, lean_object* v_ref_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3648_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3655_, lean_object* v_ref_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3655_, v_ref_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3715_; uint8_t v_beta_3716_; 
v___x_3715_ = l_Lean_Meta_Context_config(v___y_3664_);
v_beta_3716_ = lean_ctor_get_uint8(v___x_3715_, 13);
if (v_beta_3716_ == 0)
{
lean_dec_ref(v___x_3715_);
goto v___jp_3669_;
}
else
{
uint8_t v_iota_3717_; 
v_iota_3717_ = lean_ctor_get_uint8(v___x_3715_, 12);
if (v_iota_3717_ == 0)
{
lean_dec_ref(v___x_3715_);
goto v___jp_3669_;
}
else
{
uint8_t v_zeta_3718_; 
v_zeta_3718_ = lean_ctor_get_uint8(v___x_3715_, 15);
if (v_zeta_3718_ == 0)
{
lean_dec_ref(v___x_3715_);
goto v___jp_3669_;
}
else
{
uint8_t v_zetaHave_3719_; 
v_zetaHave_3719_ = lean_ctor_get_uint8(v___x_3715_, 18);
if (v_zetaHave_3719_ == 0)
{
lean_dec_ref(v___x_3715_);
goto v___jp_3669_;
}
else
{
uint8_t v_zetaDelta_3720_; 
v_zetaDelta_3720_ = lean_ctor_get_uint8(v___x_3715_, 16);
if (v_zetaDelta_3720_ == 0)
{
lean_dec_ref(v___x_3715_);
goto v___jp_3669_;
}
else
{
uint8_t v_etaStruct_3721_; uint8_t v_proj_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; 
v_etaStruct_3721_ = lean_ctor_get_uint8(v___x_3715_, 10);
v_proj_3722_ = lean_ctor_get_uint8(v___x_3715_, 14);
lean_dec_ref(v___x_3715_);
v___x_3723_ = lean_box(v_proj_3722_);
v___x_3724_ = lean_obj_tag_nat(v___x_3723_);
lean_dec(v___x_3723_);
v___x_3725_ = lean_unsigned_to_nat(2u);
v___x_3726_ = lean_nat_dec_eq(v___x_3724_, v___x_3725_);
if (v___x_3726_ == 0)
{
goto v___jp_3669_;
}
else
{
uint8_t v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = 0;
v___x_3728_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3721_, v___x_3727_);
if (v___x_3728_ == 0)
{
goto v___jp_3669_;
}
else
{
lean_object* v___x_3729_; 
v___x_3729_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec_ref(v___y_3664_);
return v___x_3729_;
}
}
}
}
}
}
}
v___jp_3669_:
{
lean_object* v___x_3670_; uint8_t v_foApprox_3671_; uint8_t v_ctxApprox_3672_; uint8_t v_quasiPatternApprox_3673_; uint8_t v_constApprox_3674_; uint8_t v_isDefEqStuckEx_3675_; uint8_t v_unificationHints_3676_; uint8_t v_proofIrrelevance_3677_; uint8_t v_assignSyntheticOpaque_3678_; uint8_t v_offsetCnstrs_3679_; uint8_t v_transparency_3680_; uint8_t v_univApprox_3681_; uint8_t v_zetaUnused_3682_; uint8_t v_canUnfoldPredicateConfig_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3714_; 
v___x_3670_ = l_Lean_Meta_Context_config(v___y_3664_);
v_foApprox_3671_ = lean_ctor_get_uint8(v___x_3670_, 0);
v_ctxApprox_3672_ = lean_ctor_get_uint8(v___x_3670_, 1);
v_quasiPatternApprox_3673_ = lean_ctor_get_uint8(v___x_3670_, 2);
v_constApprox_3674_ = lean_ctor_get_uint8(v___x_3670_, 3);
v_isDefEqStuckEx_3675_ = lean_ctor_get_uint8(v___x_3670_, 4);
v_unificationHints_3676_ = lean_ctor_get_uint8(v___x_3670_, 5);
v_proofIrrelevance_3677_ = lean_ctor_get_uint8(v___x_3670_, 6);
v_assignSyntheticOpaque_3678_ = lean_ctor_get_uint8(v___x_3670_, 7);
v_offsetCnstrs_3679_ = lean_ctor_get_uint8(v___x_3670_, 8);
v_transparency_3680_ = lean_ctor_get_uint8(v___x_3670_, 9);
v_univApprox_3681_ = lean_ctor_get_uint8(v___x_3670_, 11);
v_zetaUnused_3682_ = lean_ctor_get_uint8(v___x_3670_, 17);
v_canUnfoldPredicateConfig_3683_ = lean_ctor_get_uint8(v___x_3670_, 19);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3685_ = v___x_3670_;
v_isShared_3686_ = v_isSharedCheck_3714_;
goto v_resetjp_3684_;
}
else
{
lean_dec(v___x_3670_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3714_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
uint8_t v___x_3687_; uint8_t v___x_3688_; uint8_t v___x_3689_; lean_object* v___x_3691_; 
v___x_3687_ = 1;
v___x_3688_ = 0;
v___x_3689_ = 2;
if (v_isShared_3686_ == 0)
{
v___x_3691_ = v___x_3685_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 0, v_foApprox_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 1, v_ctxApprox_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 2, v_quasiPatternApprox_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 3, v_constApprox_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 4, v_isDefEqStuckEx_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 5, v_unificationHints_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 6, v_proofIrrelevance_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 7, v_assignSyntheticOpaque_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 8, v_offsetCnstrs_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 9, v_transparency_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 11, v_univApprox_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 17, v_zetaUnused_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3713_, 19, v_canUnfoldPredicateConfig_3683_);
v___x_3691_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
uint8_t v_trackZetaDelta_3692_; lean_object* v_zetaDeltaSet_3693_; lean_object* v_lctx_3694_; lean_object* v_localInstances_3695_; lean_object* v_defEqCtx_x3f_3696_; lean_object* v_synthPendingDepth_3697_; lean_object* v_customCanUnfoldPredicate_x3f_3698_; uint8_t v_univApprox_3699_; uint8_t v_inTypeClassResolution_3700_; uint8_t v_cacheInferType_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3711_; 
lean_ctor_set_uint8(v___x_3691_, 10, v___x_3688_);
lean_ctor_set_uint8(v___x_3691_, 12, v___x_3687_);
lean_ctor_set_uint8(v___x_3691_, 13, v___x_3687_);
lean_ctor_set_uint8(v___x_3691_, 14, v___x_3689_);
lean_ctor_set_uint8(v___x_3691_, 15, v___x_3687_);
lean_ctor_set_uint8(v___x_3691_, 16, v___x_3687_);
lean_ctor_set_uint8(v___x_3691_, 18, v___x_3687_);
v_trackZetaDelta_3692_ = lean_ctor_get_uint8(v___y_3664_, sizeof(void*)*7);
v_zetaDeltaSet_3693_ = lean_ctor_get(v___y_3664_, 1);
v_lctx_3694_ = lean_ctor_get(v___y_3664_, 2);
v_localInstances_3695_ = lean_ctor_get(v___y_3664_, 3);
v_defEqCtx_x3f_3696_ = lean_ctor_get(v___y_3664_, 4);
v_synthPendingDepth_3697_ = lean_ctor_get(v___y_3664_, 5);
v_customCanUnfoldPredicate_x3f_3698_ = lean_ctor_get(v___y_3664_, 6);
v_univApprox_3699_ = lean_ctor_get_uint8(v___y_3664_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3700_ = lean_ctor_get_uint8(v___y_3664_, sizeof(void*)*7 + 2);
v_cacheInferType_3701_ = lean_ctor_get_uint8(v___y_3664_, sizeof(void*)*7 + 3);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___y_3664_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v___y_3664_, 0);
lean_dec(v_unused_3712_);
v___x_3703_ = v___y_3664_;
v_isShared_3704_ = v_isSharedCheck_3711_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3698_);
lean_inc(v_synthPendingDepth_3697_);
lean_inc(v_defEqCtx_x3f_3696_);
lean_inc(v_localInstances_3695_);
lean_inc(v_lctx_3694_);
lean_inc(v_zetaDeltaSet_3693_);
lean_dec(v___y_3664_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3711_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
uint64_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3705_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3691_);
v___x_3706_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3706_, 0, v___x_3691_);
lean_ctor_set_uint64(v___x_3706_, sizeof(void*)*1, v___x_3705_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3706_);
v___x_3708_ = v___x_3703_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_zetaDeltaSet_3693_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_lctx_3694_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_localInstances_3695_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_defEqCtx_x3f_3696_);
lean_ctor_set(v_reuseFailAlloc_3710_, 5, v_synthPendingDepth_3697_);
lean_ctor_set(v_reuseFailAlloc_3710_, 6, v_customCanUnfoldPredicate_x3f_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*7, v_trackZetaDelta_3692_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*7 + 1, v_univApprox_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3710_, sizeof(void*)*7 + 3, v_cacheInferType_3701_);
v___x_3708_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3709_; 
v___x_3709_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3663_, v___x_3708_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec_ref(v___x_3708_);
return v___x_3709_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v___y_3744_; lean_object* v_toCold_3761_; lean_object* v_currRecDepth_3762_; lean_object* v_ref_3763_; uint16_t v_optionFlags_3764_; uint8_t v_suppressElabErrors_3765_; uint8_t v_isRecordingDeps_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3806_; 
v_toCold_3761_ = lean_ctor_get(v_a_3740_, 0);
v_currRecDepth_3762_ = lean_ctor_get(v_a_3740_, 1);
v_ref_3763_ = lean_ctor_get(v_a_3740_, 2);
v_optionFlags_3764_ = lean_ctor_get_uint16(v_a_3740_, sizeof(void*)*3);
v_suppressElabErrors_3765_ = lean_ctor_get_uint8(v_a_3740_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3766_ = lean_ctor_get_uint8(v_a_3740_, sizeof(void*)*3 + 3);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_a_3740_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3768_ = v_a_3740_;
v_isShared_3769_ = v_isSharedCheck_3806_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_ref_3763_);
lean_inc(v_currRecDepth_3762_);
lean_inc(v_toCold_3761_);
lean_dec(v_a_3740_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3806_;
goto v_resetjp_3767_;
}
v___jp_3743_:
{
if (lean_obj_tag(v___y_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
v_a_3745_ = lean_ctor_get(v___y_3744_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___y_3744_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___y_3744_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___y_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v_a_3753_ = lean_ctor_get(v___y_3744_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___y_3744_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___y_3744_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___y_3744_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
v_resetjp_3767_:
{
lean_object* v_maxRecDepth_3770_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
v_maxRecDepth_3770_ = lean_ctor_get(v_toCold_3761_, 3);
v___x_3802_ = lean_unsigned_to_nat(0u);
v___x_3803_ = lean_nat_dec_eq(v_maxRecDepth_3770_, v___x_3802_);
if (v___x_3803_ == 0)
{
uint8_t v___x_3804_; 
v___x_3804_ = lean_nat_dec_eq(v_currRecDepth_3762_, v_maxRecDepth_3770_);
if (v___x_3804_ == 0)
{
goto v___jp_3771_;
}
else
{
lean_object* v___x_3805_; 
lean_del_object(v___x_3768_);
lean_dec(v_currRecDepth_3762_);
lean_dec_ref(v_toCold_3761_);
lean_dec(v_a_3741_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec_ref(v_e_3737_);
v___x_3805_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3763_);
return v___x_3805_;
}
}
else
{
goto v___jp_3771_;
}
v___jp_3771_:
{
lean_object* v___x_3772_; uint8_t v_transparency_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
v___x_3772_ = l_Lean_Meta_Context_config(v_a_3738_);
v_transparency_3773_ = lean_ctor_get_uint8(v___x_3772_, 9);
lean_dec_ref(v___x_3772_);
v___x_3774_ = lean_unsigned_to_nat(1u);
v___x_3775_ = lean_nat_add(v_currRecDepth_3762_, v___x_3774_);
lean_dec(v_currRecDepth_3762_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v___x_3775_);
v___x_3777_ = v___x_3768_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_toCold_3761_);
lean_ctor_set(v_reuseFailAlloc_3801_, 1, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3801_, 2, v_ref_3763_);
lean_ctor_set_uint16(v_reuseFailAlloc_3801_, sizeof(void*)*3, v_optionFlags_3764_);
lean_ctor_set_uint8(v_reuseFailAlloc_3801_, sizeof(void*)*3 + 2, v_suppressElabErrors_3765_);
lean_ctor_set_uint8(v_reuseFailAlloc_3801_, sizeof(void*)*3 + 3, v_isRecordingDeps_3766_);
v___x_3777_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
uint8_t v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = 1;
v___x_3779_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3773_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3737_, v_a_3738_, v_a_3739_, v___x_3777_, v_a_3741_);
lean_dec(v_a_3741_);
lean_dec_ref(v___x_3777_);
lean_dec(v_a_3739_);
v___y_3744_ = v___x_3780_;
goto v___jp_3743_;
}
else
{
lean_object* v_keyedConfig_3781_; uint8_t v_trackZetaDelta_3782_; lean_object* v_zetaDeltaSet_3783_; lean_object* v_lctx_3784_; lean_object* v_localInstances_3785_; lean_object* v_defEqCtx_x3f_3786_; lean_object* v_synthPendingDepth_3787_; lean_object* v_customCanUnfoldPredicate_x3f_3788_; uint8_t v_univApprox_3789_; uint8_t v_inTypeClassResolution_3790_; uint8_t v_cacheInferType_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3800_; 
v_keyedConfig_3781_ = lean_ctor_get(v_a_3738_, 0);
v_trackZetaDelta_3782_ = lean_ctor_get_uint8(v_a_3738_, sizeof(void*)*7);
v_zetaDeltaSet_3783_ = lean_ctor_get(v_a_3738_, 1);
v_lctx_3784_ = lean_ctor_get(v_a_3738_, 2);
v_localInstances_3785_ = lean_ctor_get(v_a_3738_, 3);
v_defEqCtx_x3f_3786_ = lean_ctor_get(v_a_3738_, 4);
v_synthPendingDepth_3787_ = lean_ctor_get(v_a_3738_, 5);
v_customCanUnfoldPredicate_x3f_3788_ = lean_ctor_get(v_a_3738_, 6);
v_univApprox_3789_ = lean_ctor_get_uint8(v_a_3738_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3790_ = lean_ctor_get_uint8(v_a_3738_, sizeof(void*)*7 + 2);
v_cacheInferType_3791_ = lean_ctor_get_uint8(v_a_3738_, sizeof(void*)*7 + 3);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_a_3738_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3793_ = v_a_3738_;
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3788_);
lean_inc(v_synthPendingDepth_3787_);
lean_inc(v_defEqCtx_x3f_3786_);
lean_inc(v_localInstances_3785_);
lean_inc(v_lctx_3784_);
lean_inc(v_zetaDeltaSet_3783_);
lean_inc(v_keyedConfig_3781_);
lean_dec(v_a_3738_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3795_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3778_, v_keyedConfig_3781_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v___x_3795_);
v___x_3797_ = v___x_3793_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_zetaDeltaSet_3783_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_lctx_3784_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_localInstances_3785_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v_defEqCtx_x3f_3786_);
lean_ctor_set(v_reuseFailAlloc_3799_, 5, v_synthPendingDepth_3787_);
lean_ctor_set(v_reuseFailAlloc_3799_, 6, v_customCanUnfoldPredicate_x3f_3788_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*7, v_trackZetaDelta_3782_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*7 + 1, v_univApprox_3789_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3790_);
lean_ctor_set_uint8(v_reuseFailAlloc_3799_, sizeof(void*)*7 + 3, v_cacheInferType_3791_);
v___x_3797_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3737_, v___x_3797_, v_a_3739_, v___x_3777_, v_a_3741_);
lean_dec(v_a_3741_);
lean_dec_ref(v___x_3777_);
lean_dec(v_a_3739_);
v___y_3744_ = v___x_3798_;
goto v___jp_3743_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = lean_infer_type(v_e_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v_res_3813_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3814_){
_start:
{
switch(lean_obj_tag(v_x_3814_))
{
case 0:
{
uint8_t v___x_3815_; 
v___x_3815_ = 1;
return v___x_3815_;
}
case 2:
{
lean_object* v_a_3816_; lean_object* v_a_3817_; uint8_t v___x_3818_; 
v_a_3816_ = lean_ctor_get(v_x_3814_, 0);
v_a_3817_ = lean_ctor_get(v_x_3814_, 1);
v___x_3818_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3816_);
if (v___x_3818_ == 0)
{
return v___x_3818_;
}
else
{
v_x_3814_ = v_a_3817_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3820_; 
v_a_3820_ = lean_ctor_get(v_x_3814_, 1);
v_x_3814_ = v_a_3820_;
goto _start;
}
default: 
{
uint8_t v___x_3822_; 
v___x_3822_ = 0;
return v___x_3822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3823_){
_start:
{
uint8_t v_res_3824_; lean_object* v_r_3825_; 
v_res_3824_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3823_);
lean_dec(v_x_3823_);
v_r_3825_ = lean_box(v_res_3824_);
return v_r_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; lean_object* v_mctx_3830_; lean_object* v___x_3831_; lean_object* v_fst_3832_; lean_object* v_snd_3833_; lean_object* v___x_3834_; lean_object* v_cache_3835_; lean_object* v_zetaDeltaFVarIds_3836_; lean_object* v_postponed_3837_; lean_object* v_diag_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3847_; 
v___x_3829_ = lean_st_ref_get(v___y_3827_);
v_mctx_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc_ref(v_mctx_3830_);
lean_dec(v___x_3829_);
v___x_3831_ = lean_instantiate_level_mvars(v_mctx_3830_, v_l_3826_);
v_fst_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_fst_3832_);
v_snd_3833_ = lean_ctor_get(v___x_3831_, 1);
lean_inc(v_snd_3833_);
lean_dec_ref(v___x_3831_);
v___x_3834_ = lean_st_ref_take(v___y_3827_);
v_cache_3835_ = lean_ctor_get(v___x_3834_, 1);
v_zetaDeltaFVarIds_3836_ = lean_ctor_get(v___x_3834_, 2);
v_postponed_3837_ = lean_ctor_get(v___x_3834_, 3);
v_diag_3838_ = lean_ctor_get(v___x_3834_, 4);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; 
v_unused_3848_ = lean_ctor_get(v___x_3834_, 0);
lean_dec(v_unused_3848_);
v___x_3840_ = v___x_3834_;
v_isShared_3841_ = v_isSharedCheck_3847_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_diag_3838_);
lean_inc(v_postponed_3837_);
lean_inc(v_zetaDeltaFVarIds_3836_);
lean_inc(v_cache_3835_);
lean_dec(v___x_3834_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3847_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_fst_3832_);
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_fst_3832_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_cache_3835_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_zetaDeltaFVarIds_3836_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v_postponed_3837_);
lean_ctor_set(v_reuseFailAlloc_3846_, 4, v_diag_3838_);
v___x_3843_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3844_ = lean_st_ref_put(v___y_3827_, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3845_, 0, v_snd_3833_);
return v___x_3845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3849_, v___y_3850_);
lean_dec(v___y_3850_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3853_, v___y_3855_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3867_, lean_object* v_x_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
switch(lean_obj_tag(v_x_3867_))
{
case 3:
{
lean_object* v_u_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v_u_3878_ = lean_ctor_get(v_x_3867_, 0);
lean_inc(v_u_3878_);
lean_dec_ref_known(v_x_3867_, 1);
v___x_3879_ = lean_unsigned_to_nat(0u);
v___x_3880_ = lean_nat_dec_eq(v_x_3868_, v___x_3879_);
lean_dec(v_x_3868_);
if (v___x_3880_ == 0)
{
lean_dec(v_u_3878_);
goto v___jp_3874_;
}
else
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3878_, v_a_3870_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3892_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3892_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3892_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
uint8_t v___x_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3890_; 
v___x_3886_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3882_);
lean_dec(v_a_3882_);
v___x_3887_ = l_Lean_Bool_toLBool(v___x_3886_);
v___x_3888_ = lean_box(v___x_3887_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3888_);
v___x_3890_ = v___x_3884_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
v_a_3893_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3881_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3881_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3901_; lean_object* v_zero_3902_; uint8_t v_isZero_3903_; 
v_body_3901_ = lean_ctor_get(v_x_3867_, 2);
lean_inc_ref(v_body_3901_);
lean_dec_ref_known(v_x_3867_, 3);
v_zero_3902_ = lean_unsigned_to_nat(0u);
v_isZero_3903_ = lean_nat_dec_eq(v_x_3868_, v_zero_3902_);
if (v_isZero_3903_ == 1)
{
uint8_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
lean_dec_ref(v_body_3901_);
lean_dec(v_x_3868_);
v___x_3904_ = 0;
v___x_3905_ = lean_box(v___x_3904_);
v___x_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
return v___x_3906_;
}
else
{
lean_object* v_one_3907_; lean_object* v_n_3908_; 
v_one_3907_ = lean_unsigned_to_nat(1u);
v_n_3908_ = lean_nat_sub(v_x_3868_, v_one_3907_);
lean_dec(v_x_3868_);
v_x_3867_ = v_body_3901_;
v_x_3868_ = v_n_3908_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3910_; 
v_body_3910_ = lean_ctor_get(v_x_3867_, 3);
lean_inc_ref(v_body_3910_);
lean_dec_ref_known(v_x_3867_, 4);
v_x_3867_ = v_body_3910_;
goto _start;
}
case 10:
{
lean_object* v_expr_3912_; 
v_expr_3912_ = lean_ctor_get(v_x_3867_, 1);
lean_inc_ref(v_expr_3912_);
lean_dec_ref_known(v_x_3867_, 2);
v_x_3867_ = v_expr_3912_;
goto _start;
}
default: 
{
lean_dec(v_x_3868_);
lean_dec_ref(v_x_3867_);
goto v___jp_3874_;
}
}
v___jp_3874_:
{
uint8_t v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3875_ = 2;
v___x_3876_ = lean_box(v___x_3875_);
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
return v___x_3877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3914_, lean_object* v_x_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3914_, v_x_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3922_, lean_object* v_x_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_){
_start:
{
switch(lean_obj_tag(v_x_3922_))
{
case 4:
{
lean_object* v_declName_3929_; lean_object* v_us_3930_; lean_object* v___x_3931_; 
v_declName_3929_ = lean_ctor_get(v_x_3922_, 0);
lean_inc(v_declName_3929_);
v_us_3930_ = lean_ctor_get(v_x_3922_, 1);
lean_inc(v_us_3930_);
lean_dec_ref_known(v_x_3922_, 2);
v___x_3931_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3929_, v_us_3930_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3933_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3932_, v_x_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v___x_3933_;
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec(v_x_3923_);
v_a_3934_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3931_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3931_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3942_; lean_object* v___x_3943_; 
v_fvarId_3942_ = lean_ctor_get(v_x_3922_, 0);
lean_inc(v_fvarId_3942_);
lean_dec_ref_known(v_x_3922_, 1);
v___x_3943_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3942_, v_a_3924_, v_a_3926_, v_a_3927_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3944_, v_x_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v___x_3945_;
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v_x_3923_);
v_a_3946_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3943_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3943_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3954_; lean_object* v___x_3955_; 
v_mvarId_3954_ = lean_ctor_get(v_x_3922_, 0);
lean_inc(v_mvarId_3954_);
lean_dec_ref_known(v_x_3922_, 1);
v___x_3955_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3954_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3957_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3956_, v_x_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v___x_3957_;
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec(v_x_3923_);
v_a_3958_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3955_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3955_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
case 5:
{
lean_object* v_fn_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_fn_3966_ = lean_ctor_get(v_x_3922_, 0);
lean_inc_ref(v_fn_3966_);
lean_dec_ref_known(v_x_3922_, 2);
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = lean_nat_add(v_x_3923_, v___x_3967_);
lean_dec(v_x_3923_);
v_x_3922_ = v_fn_3966_;
v_x_3923_ = v___x_3968_;
goto _start;
}
case 10:
{
lean_object* v_expr_3970_; 
v_expr_3970_ = lean_ctor_get(v_x_3922_, 1);
lean_inc_ref(v_expr_3970_);
lean_dec_ref_known(v_x_3922_, 2);
v_x_3922_ = v_expr_3970_;
goto _start;
}
case 8:
{
lean_object* v_body_3972_; 
v_body_3972_ = lean_ctor_get(v_x_3922_, 3);
lean_inc_ref(v_body_3972_);
lean_dec_ref_known(v_x_3922_, 4);
v_x_3922_ = v_body_3972_;
goto _start;
}
case 6:
{
lean_object* v_body_3974_; lean_object* v_zero_3975_; uint8_t v_isZero_3976_; 
v_body_3974_ = lean_ctor_get(v_x_3922_, 2);
lean_inc_ref(v_body_3974_);
lean_dec_ref_known(v_x_3922_, 3);
v_zero_3975_ = lean_unsigned_to_nat(0u);
v_isZero_3976_ = lean_nat_dec_eq(v_x_3923_, v_zero_3975_);
if (v_isZero_3976_ == 1)
{
uint8_t v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_dec_ref(v_body_3974_);
lean_dec(v_x_3923_);
v___x_3977_ = 0;
v___x_3978_ = lean_box(v___x_3977_);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
else
{
lean_object* v_one_3980_; lean_object* v_n_3981_; 
v_one_3980_ = lean_unsigned_to_nat(1u);
v_n_3981_ = lean_nat_sub(v_x_3923_, v_one_3980_);
lean_dec(v_x_3923_);
v_x_3922_ = v_body_3974_;
v_x_3923_ = v_n_3981_;
goto _start;
}
}
default: 
{
uint8_t v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_dec(v_x_3923_);
lean_dec_ref(v_x_3922_);
v___x_3983_ = 2;
v___x_3984_ = lean_box(v___x_3983_);
v___x_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
return v___x_3985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3986_, lean_object* v_x_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3986_, v_x_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
switch(lean_obj_tag(v_x_3994_))
{
case 1:
{
lean_object* v_fvarId_4000_; lean_object* v___x_4001_; 
v_fvarId_4000_ = lean_ctor_get(v_x_3994_, 0);
lean_inc(v_fvarId_4000_);
lean_dec_ref_known(v_x_3994_, 1);
v___x_4001_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4000_, v_a_3995_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4002_, v___x_4003_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4004_;
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_4001_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4001_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4013_; lean_object* v___x_4014_; 
v_mvarId_4013_ = lean_ctor_get(v_x_3994_, 0);
lean_inc(v_mvarId_4013_);
lean_dec_ref_known(v_x_3994_, 1);
v___x_4014_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4013_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4014_, 1);
v___x_4016_ = lean_unsigned_to_nat(0u);
v___x_4017_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4015_, v___x_4016_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4017_;
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
v_a_4018_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4014_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4014_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
case 3:
{
uint8_t v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
lean_dec_ref_known(v_x_3994_, 1);
v___x_4026_ = 0;
v___x_4027_ = lean_box(v___x_4026_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
return v___x_4028_;
}
case 4:
{
lean_object* v_declName_4029_; lean_object* v_us_4030_; lean_object* v___x_4031_; 
v_declName_4029_ = lean_ctor_get(v_x_3994_, 0);
lean_inc(v_declName_4029_);
v_us_4030_ = lean_ctor_get(v_x_3994_, 1);
lean_inc(v_us_4030_);
lean_dec_ref_known(v_x_3994_, 2);
v___x_4031_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4029_, v_us_4030_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v___x_4033_ = lean_unsigned_to_nat(0u);
v___x_4034_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4032_, v___x_4033_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4034_;
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_a_4035_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4031_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4031_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
case 5:
{
lean_object* v_fn_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v_fn_4043_ = lean_ctor_get(v_x_3994_, 0);
lean_inc_ref(v_fn_4043_);
lean_dec_ref_known(v_x_3994_, 2);
v___x_4044_ = lean_unsigned_to_nat(1u);
v___x_4045_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4043_, v___x_4044_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
return v___x_4045_;
}
case 6:
{
uint8_t v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_dec_ref_known(v_x_3994_, 3);
v___x_4046_ = 0;
v___x_4047_ = lean_box(v___x_4046_);
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
case 7:
{
lean_object* v_body_4049_; 
v_body_4049_ = lean_ctor_get(v_x_3994_, 2);
lean_inc_ref(v_body_4049_);
lean_dec_ref_known(v_x_3994_, 3);
v_x_3994_ = v_body_4049_;
goto _start;
}
case 8:
{
lean_object* v_body_4051_; 
v_body_4051_ = lean_ctor_get(v_x_3994_, 3);
lean_inc_ref(v_body_4051_);
lean_dec_ref_known(v_x_3994_, 4);
v_x_3994_ = v_body_4051_;
goto _start;
}
case 9:
{
uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_dec_ref_known(v_x_3994_, 1);
v___x_4053_ = 0;
v___x_4054_ = lean_box(v___x_4053_);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
case 10:
{
lean_object* v_expr_4056_; 
v_expr_4056_ = lean_ctor_get(v_x_3994_, 1);
lean_inc_ref(v_expr_4056_);
lean_dec_ref_known(v_x_3994_, 2);
v_x_3994_ = v_expr_4056_;
goto _start;
}
default: 
{
uint8_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_dec_ref(v_x_3994_);
v___x_4058_ = 2;
v___x_4059_ = lean_box(v___x_4058_);
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
return v___x_4060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_Meta_isPropQuick(v_x_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v___x_4074_; 
lean_inc_ref(v_e_4068_);
v___x_4074_ = l_Lean_Meta_isPropQuick(v_e_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4131_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4077_ = v___x_4074_;
v_isShared_4078_ = v_isSharedCheck_4131_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4131_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
uint8_t v___x_4079_; 
v___x_4079_ = lean_unbox(v_a_4075_);
lean_dec(v_a_4075_);
switch(v___x_4079_)
{
case 0:
{
uint8_t v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4083_; 
lean_dec_ref(v_e_4068_);
v___x_4080_ = 0;
v___x_4081_ = lean_box(v___x_4080_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 0, v___x_4081_);
v___x_4083_ = v___x_4077_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
case 1:
{
uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
lean_dec_ref(v_e_4068_);
v___x_4085_ = 1;
v___x_4086_ = lean_box(v___x_4085_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 0, v___x_4086_);
v___x_4088_ = v___x_4077_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
default: 
{
lean_object* v___x_4090_; 
lean_del_object(v___x_4077_);
lean_inc(v_a_4072_);
lean_inc_ref(v_a_4071_);
lean_inc(v_a_4070_);
lean_inc_ref(v_a_4069_);
v___x_4090_ = lean_infer_type(v_e_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4092_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
v___x_4092_ = l_Lean_Meta_whnfD(v_a_4091_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4114_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4114_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4114_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
if (lean_obj_tag(v_a_4093_) == 3)
{
lean_object* v_u_4097_; lean_object* v___x_4098_; lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4108_; 
lean_del_object(v___x_4095_);
v_u_4097_ = lean_ctor_get(v_a_4093_, 0);
lean_inc(v_u_4097_);
lean_dec_ref_known(v_a_4093_, 1);
v___x_4098_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4097_, v_a_4070_);
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4101_ = v___x_4098_;
v_isShared_4102_ = v_isSharedCheck_4108_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4108_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
uint8_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
v___x_4103_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4099_);
lean_dec(v_a_4099_);
v___x_4104_ = lean_box(v___x_4103_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4104_);
v___x_4106_ = v___x_4101_;
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
}
else
{
uint8_t v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
lean_dec(v_a_4093_);
v___x_4109_ = 0;
v___x_4110_ = lean_box(v___x_4109_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4110_);
v___x_4112_ = v___x_4095_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
v_a_4115_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4092_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4092_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
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
v_a_4123_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4090_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4090_);
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
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec_ref(v_e_4068_);
v_a_4132_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4074_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4074_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Meta_isProp(v_e_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4147_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_obj_tag_nat(v_x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4149_);
lean_dec(v_x_4149_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4151_, lean_object* v_k_4152_){
_start:
{
if (lean_obj_tag(v_t_4151_) == 3)
{
lean_object* v_idx_4153_; lean_object* v_numArgs_4154_; lean_object* v___x_4155_; 
v_idx_4153_ = lean_ctor_get(v_t_4151_, 0);
lean_inc(v_idx_4153_);
v_numArgs_4154_ = lean_ctor_get(v_t_4151_, 1);
lean_inc(v_numArgs_4154_);
lean_dec_ref_known(v_t_4151_, 2);
v___x_4155_ = lean_apply_2(v_k_4152_, v_idx_4153_, v_numArgs_4154_);
return v___x_4155_;
}
else
{
lean_dec(v_t_4151_);
return v_k_4152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4156_, lean_object* v_ctorIdx_4157_, lean_object* v_t_4158_, lean_object* v_h_4159_, lean_object* v_k_4160_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4158_, v_k_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4162_, lean_object* v_ctorIdx_4163_, lean_object* v_t_4164_, lean_object* v_h_4165_, lean_object* v_k_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4162_, v_ctorIdx_4163_, v_t_4164_, v_h_4165_, v_k_4166_);
lean_dec(v_ctorIdx_4163_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4168_, lean_object* v_false_4169_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4168_, v_false_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4171_, lean_object* v_t_4172_, lean_object* v_h_4173_, lean_object* v_false_4174_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4172_, v_false_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4176_, lean_object* v_true_4177_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4176_, v_true_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4179_, lean_object* v_t_4180_, lean_object* v_h_4181_, lean_object* v_true_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4180_, v_true_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4184_, lean_object* v_undef_4185_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4184_, v_undef_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4187_, lean_object* v_t_4188_, lean_object* v_h_4189_, lean_object* v_undef_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4188_, v_undef_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4192_, lean_object* v_bvar_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4192_, v_bvar_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4195_, lean_object* v_t_4196_, lean_object* v_h_4197_, lean_object* v_bvar_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4196_, v_bvar_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4200_){
_start:
{
switch(v_x_4200_)
{
case 0:
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_box(0);
return v___x_4201_;
}
case 1:
{
lean_object* v___x_4202_; 
v___x_4202_ = lean_box(1);
return v___x_4202_;
}
default: 
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_box(2);
return v___x_4203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4204_){
_start:
{
uint8_t v_x_25__boxed_4205_; lean_object* v_res_4206_; 
v_x_25__boxed_4205_ = lean_unbox(v_x_4204_);
v_res_4206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4205_);
return v_res_4206_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4207_){
_start:
{
switch(lean_obj_tag(v_x_4207_))
{
case 0:
{
uint8_t v___x_4208_; 
v___x_4208_ = 0;
return v___x_4208_;
}
case 1:
{
uint8_t v___x_4209_; 
v___x_4209_ = 1;
return v___x_4209_;
}
default: 
{
uint8_t v___x_4210_; 
v___x_4210_ = 2;
return v___x_4210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4211_){
_start:
{
uint8_t v_res_4212_; lean_object* v_r_4213_; 
v_res_4212_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4211_);
lean_dec(v_x_4211_);
v_r_4213_ = lean_box(v_res_4212_);
return v_r_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4215_, lean_object* v_numArgs_4216_){
_start:
{
switch(lean_obj_tag(v_e_4215_))
{
case 3:
{
lean_object* v_u_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v_u_4217_ = lean_ctor_get(v_e_4215_, 0);
v___x_4218_ = lean_unsigned_to_nat(0u);
v___x_4219_ = lean_nat_dec_eq(v_numArgs_4216_, v___x_4218_);
lean_dec(v_numArgs_4216_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4220_; 
v___x_4220_ = lean_box(2);
return v___x_4220_;
}
else
{
uint8_t v___x_4221_; 
v___x_4221_ = l_Lean_Level_isNeverZero(v_u_4217_);
if (v___x_4221_ == 0)
{
uint8_t v___x_4222_; 
v___x_4222_ = l_Lean_Level_isZero(v_u_4217_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_box(2);
return v___x_4223_;
}
else
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_box(1);
return v___x_4224_;
}
}
else
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_box(0);
return v___x_4225_;
}
}
}
case 7:
{
lean_object* v_body_4226_; lean_object* v_zero_4227_; uint8_t v_isZero_4228_; 
v_body_4226_ = lean_ctor_get(v_e_4215_, 2);
v_zero_4227_ = lean_unsigned_to_nat(0u);
v_isZero_4228_ = lean_nat_dec_eq(v_numArgs_4216_, v_zero_4227_);
if (v_isZero_4228_ == 0)
{
lean_object* v_one_4229_; lean_object* v_n_4230_; 
v_one_4229_ = lean_unsigned_to_nat(1u);
v_n_4230_ = lean_nat_sub(v_numArgs_4216_, v_one_4229_);
lean_dec(v_numArgs_4216_);
v_e_4215_ = v_body_4226_;
v_numArgs_4216_ = v_n_4230_;
goto _start;
}
else
{
lean_object* v___x_4232_; 
lean_dec(v_numArgs_4216_);
v___x_4232_ = lean_box(2);
return v___x_4232_;
}
}
case 10:
{
lean_object* v_expr_4233_; 
v_expr_4233_ = lean_ctor_get(v_e_4215_, 1);
v_e_4215_ = v_expr_4233_;
goto _start;
}
case 5:
{
lean_object* v_fn_4235_; 
v_fn_4235_ = lean_ctor_get(v_e_4215_, 0);
if (lean_obj_tag(v_fn_4235_) == 4)
{
lean_object* v_declName_4236_; 
v_declName_4236_ = lean_ctor_get(v_fn_4235_, 0);
if (lean_obj_tag(v_declName_4236_) == 1)
{
lean_object* v_pre_4237_; 
v_pre_4237_ = lean_ctor_get(v_declName_4236_, 0);
if (lean_obj_tag(v_pre_4237_) == 0)
{
lean_object* v_arg_4238_; lean_object* v_str_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v_arg_4238_ = lean_ctor_get(v_e_4215_, 1);
v_str_4239_ = lean_ctor_get(v_declName_4236_, 1);
v___x_4240_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4241_ = lean_string_dec_eq(v_str_4239_, v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; 
lean_dec(v_numArgs_4216_);
v___x_4242_ = lean_box(2);
return v___x_4242_;
}
else
{
v_e_4215_ = v_arg_4238_;
goto _start;
}
}
else
{
lean_object* v___x_4244_; 
lean_dec(v_numArgs_4216_);
v___x_4244_ = lean_box(2);
return v___x_4244_;
}
}
else
{
lean_object* v___x_4245_; 
lean_dec(v_numArgs_4216_);
v___x_4245_ = lean_box(2);
return v___x_4245_;
}
}
else
{
lean_object* v___x_4246_; 
lean_dec(v_numArgs_4216_);
v___x_4246_ = lean_box(2);
return v___x_4246_;
}
}
default: 
{
lean_object* v___x_4247_; 
lean_dec(v_numArgs_4216_);
v___x_4247_ = lean_box(2);
return v___x_4247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4248_, lean_object* v_numArgs_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4248_, v_numArgs_4249_);
lean_dec_ref(v_e_4248_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4251_, lean_object* v_binderType_4252_){
_start:
{
if (lean_obj_tag(v_r_4251_) == 3)
{
lean_object* v_idx_4253_; lean_object* v_numArgs_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4266_; 
v_idx_4253_ = lean_ctor_get(v_r_4251_, 0);
v_numArgs_4254_ = lean_ctor_get(v_r_4251_, 1);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_r_4251_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4256_ = v_r_4251_;
v_isShared_4257_ = v_isSharedCheck_4266_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_numArgs_4254_);
lean_inc(v_idx_4253_);
lean_dec(v_r_4251_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4266_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v_zero_4258_; uint8_t v_isZero_4259_; 
v_zero_4258_ = lean_unsigned_to_nat(0u);
v_isZero_4259_ = lean_nat_dec_eq(v_idx_4253_, v_zero_4258_);
if (v_isZero_4259_ == 1)
{
lean_object* v___x_4260_; 
lean_del_object(v___x_4256_);
lean_dec(v_idx_4253_);
v___x_4260_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4252_, v_numArgs_4254_);
return v___x_4260_;
}
else
{
lean_object* v_one_4261_; lean_object* v_n_4262_; lean_object* v___x_4264_; 
v_one_4261_ = lean_unsigned_to_nat(1u);
v_n_4262_ = lean_nat_sub(v_idx_4253_, v_one_4261_);
lean_dec(v_idx_4253_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v_n_4262_);
v___x_4264_ = v___x_4256_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_n_4262_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_numArgs_4254_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
else
{
return v_r_4251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4267_, lean_object* v_binderType_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4267_, v_binderType_4268_);
lean_dec_ref(v_binderType_4268_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4270_, lean_object* v_x_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v_type_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; 
switch(lean_obj_tag(v_x_4270_))
{
case 7:
{
lean_object* v_binderType_4310_; lean_object* v_body_4311_; lean_object* v_zero_4312_; uint8_t v_isZero_4313_; 
v_binderType_4310_ = lean_ctor_get(v_x_4270_, 1);
v_body_4311_ = lean_ctor_get(v_x_4270_, 2);
v_zero_4312_ = lean_unsigned_to_nat(0u);
v_isZero_4313_ = lean_nat_dec_eq(v_x_4271_, v_zero_4312_);
if (v_isZero_4313_ == 1)
{
v_type_4278_ = v_x_4270_;
v___y_4279_ = v_a_4272_;
v___y_4280_ = v_a_4273_;
v___y_4281_ = v_a_4274_;
v___y_4282_ = v_a_4275_;
goto v___jp_4277_;
}
else
{
lean_object* v_one_4314_; lean_object* v_n_4315_; lean_object* v___x_4316_; 
lean_inc_ref(v_body_4311_);
lean_inc_ref(v_binderType_4310_);
lean_dec_ref_known(v_x_4270_, 3);
v_one_4314_ = lean_unsigned_to_nat(1u);
v_n_4315_ = lean_nat_sub(v_x_4271_, v_one_4314_);
v___x_4316_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4311_, v_n_4315_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
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
v_type_4326_ = lean_ctor_get(v_x_4270_, 1);
lean_inc_ref(v_type_4326_);
v_body_4327_ = lean_ctor_get(v_x_4270_, 3);
lean_inc_ref(v_body_4327_);
lean_dec_ref_known(v_x_4270_, 4);
v___x_4328_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4327_, v_x_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
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
v_expr_4338_ = lean_ctor_get(v_x_4270_, 1);
lean_inc_ref(v_expr_4338_);
lean_dec_ref_known(v_x_4270_, 2);
v_x_4270_ = v_expr_4338_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4340_; lean_object* v___x_4341_; uint8_t v___x_4342_; 
v_deBruijnIndex_4340_ = lean_ctor_get(v_x_4270_, 0);
lean_inc(v_deBruijnIndex_4340_);
lean_dec_ref_known(v_x_4270_, 1);
v___x_4341_ = lean_unsigned_to_nat(0u);
v___x_4342_ = lean_nat_dec_eq(v_x_4271_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_dec(v_deBruijnIndex_4340_);
goto v___jp_4307_;
}
else
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4343_, 0, v_deBruijnIndex_4340_);
lean_ctor_set(v___x_4343_, 1, v___x_4341_);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
return v___x_4344_;
}
}
default: 
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = lean_nat_dec_eq(v_x_4271_, v___x_4345_);
if (v___x_4346_ == 0)
{
lean_dec_ref(v_x_4270_);
goto v___jp_4307_;
}
else
{
v_type_4278_ = v_x_4270_;
v___y_4279_ = v_a_4272_;
v___y_4280_ = v_a_4273_;
v___y_4281_ = v_a_4274_;
v___y_4282_ = v_a_4275_;
goto v___jp_4277_;
}
}
}
v___jp_4277_:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_Expr_getAppFn(v_type_4278_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_deBruijnIndex_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_deBruijnIndex_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_deBruijnIndex_4284_);
lean_dec_ref_known(v___x_4283_, 1);
v___x_4285_ = l_Lean_Expr_getAppNumArgs(v_type_4278_);
lean_dec_ref(v_type_4278_);
v___x_4286_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4286_, 0, v_deBruijnIndex_4284_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
else
{
lean_object* v___x_4288_; 
lean_dec_ref(v___x_4283_);
v___x_4288_ = l_Lean_Meta_isPropQuick(v_type_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
switch(lean_obj_tag(v_x_4389_))
{
case 1:
{
lean_object* v_fvarId_4395_; lean_object* v___x_4396_; 
v_fvarId_4395_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_fvarId_4395_);
lean_dec_ref_known(v_x_4389_, 1);
v___x_4396_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4395_, v_a_4390_, v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4397_, v___x_4398_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
return v___x_4399_;
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
v_a_4400_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4396_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4396_);
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
case 2:
{
lean_object* v_mvarId_4408_; lean_object* v___x_4409_; 
v_mvarId_4408_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_mvarId_4408_);
lean_dec_ref_known(v_x_4389_, 1);
v___x_4409_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4408_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = lean_unsigned_to_nat(0u);
v___x_4412_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4410_, v___x_4411_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
return v___x_4412_;
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
v_a_4413_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4409_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4409_);
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
case 3:
{
uint8_t v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_dec_ref_known(v_x_4389_, 1);
v___x_4421_ = 0;
v___x_4422_ = lean_box(v___x_4421_);
v___x_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
return v___x_4423_;
}
case 4:
{
lean_object* v_declName_4424_; lean_object* v_us_4425_; lean_object* v___x_4426_; 
v_declName_4424_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_declName_4424_);
v_us_4425_ = lean_ctor_get(v_x_4389_, 1);
lean_inc(v_us_4425_);
lean_dec_ref_known(v_x_4389_, 2);
v___x_4426_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4424_, v_us_4425_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
v___x_4428_ = lean_unsigned_to_nat(0u);
v___x_4429_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4427_, v___x_4428_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
return v___x_4429_;
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_a_4430_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4426_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4426_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
case 5:
{
lean_object* v_fn_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v_fn_4438_ = lean_ctor_get(v_x_4389_, 0);
lean_inc_ref(v_fn_4438_);
lean_dec_ref_known(v_x_4389_, 2);
v___x_4439_ = lean_unsigned_to_nat(1u);
v___x_4440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4438_, v___x_4439_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
return v___x_4440_;
}
case 6:
{
lean_object* v_body_4441_; 
v_body_4441_ = lean_ctor_get(v_x_4389_, 2);
lean_inc_ref(v_body_4441_);
lean_dec_ref_known(v_x_4389_, 3);
v_x_4389_ = v_body_4441_;
goto _start;
}
case 7:
{
uint8_t v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
lean_dec_ref_known(v_x_4389_, 3);
v___x_4443_ = 0;
v___x_4444_ = lean_box(v___x_4443_);
v___x_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4444_);
return v___x_4445_;
}
case 8:
{
lean_object* v_body_4446_; 
v_body_4446_ = lean_ctor_get(v_x_4389_, 3);
lean_inc_ref(v_body_4446_);
lean_dec_ref_known(v_x_4389_, 4);
v_x_4389_ = v_body_4446_;
goto _start;
}
case 9:
{
uint8_t v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_dec_ref_known(v_x_4389_, 1);
v___x_4448_ = 0;
v___x_4449_ = lean_box(v___x_4448_);
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
return v___x_4450_;
}
case 10:
{
lean_object* v_expr_4451_; 
v_expr_4451_ = lean_ctor_get(v_x_4389_, 1);
lean_inc_ref(v_expr_4451_);
lean_dec_ref_known(v_x_4389_, 2);
v_x_4389_ = v_expr_4451_;
goto _start;
}
default: 
{
uint8_t v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_dec_ref(v_x_4389_);
v___x_4453_ = 2;
v___x_4454_ = lean_box(v___x_4453_);
v___x_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4454_);
return v___x_4455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4456_, lean_object* v_x_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
switch(lean_obj_tag(v_x_4456_))
{
case 4:
{
lean_object* v_declName_4463_; lean_object* v_us_4464_; lean_object* v___x_4465_; 
v_declName_4463_ = lean_ctor_get(v_x_4456_, 0);
lean_inc(v_declName_4463_);
v_us_4464_ = lean_ctor_get(v_x_4456_, 1);
lean_inc(v_us_4464_);
lean_dec_ref_known(v_x_4456_, 2);
v___x_4465_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4463_, v_us_4464_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4467_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4467_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4466_, v_x_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_x_4457_);
return v___x_4467_;
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v_x_4457_);
v_a_4468_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4465_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4465_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4476_; lean_object* v___x_4477_; 
v_fvarId_4476_ = lean_ctor_get(v_x_4456_, 0);
lean_inc(v_fvarId_4476_);
lean_dec_ref_known(v_x_4456_, 1);
v___x_4477_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4476_, v_a_4458_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4479_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4477_, 1);
v___x_4479_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4478_, v_x_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_x_4457_);
return v___x_4479_;
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_dec(v_x_4457_);
v_a_4480_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4477_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4477_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4488_; lean_object* v___x_4489_; 
v_mvarId_4488_ = lean_ctor_get(v_x_4456_, 0);
lean_inc(v_mvarId_4488_);
lean_dec_ref_known(v_x_4456_, 1);
v___x_4489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4488_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4490_, v_x_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_x_4457_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_x_4457_);
v_a_4492_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4489_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4489_);
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
v_fn_4500_ = lean_ctor_get(v_x_4456_, 0);
lean_inc_ref(v_fn_4500_);
lean_dec_ref_known(v_x_4456_, 2);
v___x_4501_ = lean_unsigned_to_nat(1u);
v___x_4502_ = lean_nat_add(v_x_4457_, v___x_4501_);
lean_dec(v_x_4457_);
v_x_4456_ = v_fn_4500_;
v_x_4457_ = v___x_4502_;
goto _start;
}
case 10:
{
lean_object* v_expr_4504_; 
v_expr_4504_ = lean_ctor_get(v_x_4456_, 1);
lean_inc_ref(v_expr_4504_);
lean_dec_ref_known(v_x_4456_, 2);
v_x_4456_ = v_expr_4504_;
goto _start;
}
case 8:
{
lean_object* v_body_4506_; 
v_body_4506_ = lean_ctor_get(v_x_4456_, 3);
lean_inc_ref(v_body_4506_);
lean_dec_ref_known(v_x_4456_, 4);
v_x_4456_ = v_body_4506_;
goto _start;
}
case 6:
{
lean_object* v_body_4508_; lean_object* v_zero_4509_; uint8_t v_isZero_4510_; 
v_body_4508_ = lean_ctor_get(v_x_4456_, 2);
lean_inc_ref(v_body_4508_);
lean_dec_ref_known(v_x_4456_, 3);
v_zero_4509_ = lean_unsigned_to_nat(0u);
v_isZero_4510_ = lean_nat_dec_eq(v_x_4457_, v_zero_4509_);
if (v_isZero_4510_ == 1)
{
lean_object* v___x_4511_; 
lean_dec(v_x_4457_);
v___x_4511_ = l_Lean_Meta_isProofQuick(v_body_4508_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
return v___x_4511_;
}
else
{
lean_object* v_one_4512_; lean_object* v_n_4513_; 
v_one_4512_ = lean_unsigned_to_nat(1u);
v_n_4513_ = lean_nat_sub(v_x_4457_, v_one_4512_);
lean_dec(v_x_4457_);
v_x_4456_ = v_body_4508_;
v_x_4457_ = v_n_4513_;
goto _start;
}
}
default: 
{
uint8_t v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
lean_dec(v_x_4457_);
lean_dec_ref(v_x_4456_);
v___x_4515_ = 2;
v___x_4516_ = lean_box(v___x_4515_);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4518_, lean_object* v_x_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4518_, v_x_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_Meta_isProofQuick(v_x_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_){
_start:
{
lean_object* v___x_4539_; 
lean_inc_ref(v_e_4533_);
v___x_4539_ = l_Lean_Meta_isProofQuick(v_e_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4566_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4542_ = v___x_4539_;
v_isShared_4543_ = v_isSharedCheck_4566_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4539_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4566_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
uint8_t v___x_4544_; 
v___x_4544_ = lean_unbox(v_a_4540_);
lean_dec(v_a_4540_);
switch(v___x_4544_)
{
case 0:
{
uint8_t v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
lean_dec_ref(v_e_4533_);
v___x_4545_ = 0;
v___x_4546_ = lean_box(v___x_4545_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___x_4546_);
v___x_4548_ = v___x_4542_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
case 1:
{
uint8_t v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4553_; 
lean_dec_ref(v_e_4533_);
v___x_4550_ = 1;
v___x_4551_ = lean_box(v___x_4550_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___x_4551_);
v___x_4553_ = v___x_4542_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
default: 
{
lean_object* v___x_4555_; 
lean_del_object(v___x_4542_);
lean_inc(v_a_4537_);
lean_inc_ref(v_a_4536_);
lean_inc(v_a_4535_);
lean_inc_ref(v_a_4534_);
v___x_4555_ = lean_infer_type(v_e_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref_known(v___x_4555_, 1);
v___x_4557_ = l_Lean_Meta_isProp(v_a_4556_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
return v___x_4557_;
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
v_a_4558_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4555_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4555_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4574_; 
lean_dec_ref(v_e_4533_);
v_a_4567_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4569_ = v___x_4539_;
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4539_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4572_; 
if (v_isShared_4570_ == 0)
{
v___x_4572_ = v___x_4569_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_Meta_isProof(v_e_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
lean_dec(v_a_4579_);
lean_dec_ref(v_a_4578_);
lean_dec(v_a_4577_);
lean_dec_ref(v_a_4576_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4582_, lean_object* v_x_4583_){
_start:
{
switch(lean_obj_tag(v_x_4582_))
{
case 3:
{
lean_object* v___x_4589_; uint8_t v___x_4590_; 
v___x_4589_ = lean_unsigned_to_nat(0u);
v___x_4590_ = lean_nat_dec_eq(v_x_4583_, v___x_4589_);
lean_dec(v_x_4583_);
if (v___x_4590_ == 0)
{
goto v___jp_4585_;
}
else
{
uint8_t v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4591_ = 1;
v___x_4592_ = lean_box(v___x_4591_);
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
}
case 7:
{
lean_object* v_body_4594_; lean_object* v_zero_4595_; uint8_t v_isZero_4596_; 
v_body_4594_ = lean_ctor_get(v_x_4582_, 2);
v_zero_4595_ = lean_unsigned_to_nat(0u);
v_isZero_4596_ = lean_nat_dec_eq(v_x_4583_, v_zero_4595_);
if (v_isZero_4596_ == 1)
{
uint8_t v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
lean_dec(v_x_4583_);
v___x_4597_ = 0;
v___x_4598_ = lean_box(v___x_4597_);
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
return v___x_4599_;
}
else
{
lean_object* v_one_4600_; lean_object* v_n_4601_; 
v_one_4600_ = lean_unsigned_to_nat(1u);
v_n_4601_ = lean_nat_sub(v_x_4583_, v_one_4600_);
lean_dec(v_x_4583_);
v_x_4582_ = v_body_4594_;
v_x_4583_ = v_n_4601_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4603_; 
v_body_4603_ = lean_ctor_get(v_x_4582_, 3);
v_x_4582_ = v_body_4603_;
goto _start;
}
case 10:
{
lean_object* v_expr_4605_; 
v_expr_4605_ = lean_ctor_get(v_x_4582_, 1);
v_x_4582_ = v_expr_4605_;
goto _start;
}
default: 
{
lean_dec(v_x_4583_);
goto v___jp_4585_;
}
}
v___jp_4585_:
{
uint8_t v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4586_ = 2;
v___x_4587_ = lean_box(v___x_4586_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4607_, lean_object* v_x_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4607_, v_x_4608_);
lean_dec_ref(v_x_4607_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4611_, lean_object* v_x_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v___x_4618_; 
v___x_4618_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4611_, v_x_4612_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4619_, lean_object* v_x_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4619_, v_x_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec_ref(v_x_4619_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4627_, lean_object* v_x_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
switch(lean_obj_tag(v_x_4627_))
{
case 4:
{
lean_object* v_declName_4634_; lean_object* v_us_4635_; lean_object* v___x_4636_; 
v_declName_4634_ = lean_ctor_get(v_x_4627_, 0);
lean_inc(v_declName_4634_);
v_us_4635_ = lean_ctor_get(v_x_4627_, 1);
lean_inc(v_us_4635_);
lean_dec_ref_known(v_x_4627_, 2);
v___x_4636_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4634_, v_us_4635_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4638_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4636_, 1);
v___x_4638_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4637_, v_x_4628_);
lean_dec(v_a_4637_);
return v___x_4638_;
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec(v_x_4628_);
v_a_4639_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4636_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4636_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4647_; lean_object* v___x_4648_; 
v_fvarId_4647_ = lean_ctor_get(v_x_4627_, 0);
lean_inc(v_fvarId_4647_);
lean_dec_ref_known(v_x_4627_, 1);
v___x_4648_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4647_, v_a_4629_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4650_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
lean_inc(v_a_4649_);
lean_dec_ref_known(v___x_4648_, 1);
v___x_4650_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4649_, v_x_4628_);
lean_dec(v_a_4649_);
return v___x_4650_;
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
lean_dec(v_x_4628_);
v_a_4651_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4648_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4648_);
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
case 2:
{
lean_object* v_mvarId_4659_; lean_object* v___x_4660_; 
v_mvarId_4659_ = lean_ctor_get(v_x_4627_, 0);
lean_inc(v_mvarId_4659_);
lean_dec_ref_known(v_x_4627_, 1);
v___x_4660_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4659_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4662_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v___x_4662_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4661_, v_x_4628_);
lean_dec(v_a_4661_);
return v___x_4662_;
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec(v_x_4628_);
v_a_4663_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4660_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4660_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
case 5:
{
lean_object* v_fn_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v_fn_4671_ = lean_ctor_get(v_x_4627_, 0);
lean_inc_ref(v_fn_4671_);
lean_dec_ref_known(v_x_4627_, 2);
v___x_4672_ = lean_unsigned_to_nat(1u);
v___x_4673_ = lean_nat_add(v_x_4628_, v___x_4672_);
lean_dec(v_x_4628_);
v_x_4627_ = v_fn_4671_;
v_x_4628_ = v___x_4673_;
goto _start;
}
case 10:
{
lean_object* v_expr_4675_; 
v_expr_4675_ = lean_ctor_get(v_x_4627_, 1);
lean_inc_ref(v_expr_4675_);
lean_dec_ref_known(v_x_4627_, 2);
v_x_4627_ = v_expr_4675_;
goto _start;
}
case 8:
{
lean_object* v_body_4677_; 
v_body_4677_ = lean_ctor_get(v_x_4627_, 3);
lean_inc_ref(v_body_4677_);
lean_dec_ref_known(v_x_4627_, 4);
v_x_4627_ = v_body_4677_;
goto _start;
}
case 6:
{
lean_object* v_body_4679_; lean_object* v_zero_4680_; uint8_t v_isZero_4681_; 
v_body_4679_ = lean_ctor_get(v_x_4627_, 2);
lean_inc_ref(v_body_4679_);
lean_dec_ref_known(v_x_4627_, 3);
v_zero_4680_ = lean_unsigned_to_nat(0u);
v_isZero_4681_ = lean_nat_dec_eq(v_x_4628_, v_zero_4680_);
if (v_isZero_4681_ == 1)
{
uint8_t v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
lean_dec_ref(v_body_4679_);
lean_dec(v_x_4628_);
v___x_4682_ = 0;
v___x_4683_ = lean_box(v___x_4682_);
v___x_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
return v___x_4684_;
}
else
{
lean_object* v_one_4685_; lean_object* v_n_4686_; 
v_one_4685_ = lean_unsigned_to_nat(1u);
v_n_4686_ = lean_nat_sub(v_x_4628_, v_one_4685_);
lean_dec(v_x_4628_);
v_x_4627_ = v_body_4679_;
v_x_4628_ = v_n_4686_;
goto _start;
}
}
default: 
{
uint8_t v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_dec(v_x_4628_);
lean_dec_ref(v_x_4627_);
v___x_4688_ = 2;
v___x_4689_ = lean_box(v___x_4688_);
v___x_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
return v___x_4690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4691_, lean_object* v_x_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4691_, v_x_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
switch(lean_obj_tag(v_x_4699_))
{
case 1:
{
lean_object* v_fvarId_4705_; lean_object* v___x_4706_; 
v_fvarId_4705_ = lean_ctor_get(v_x_4699_, 0);
lean_inc(v_fvarId_4705_);
lean_dec_ref_known(v_x_4699_, 1);
v___x_4706_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4705_, v_a_4700_, v_a_4702_, v_a_4703_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4706_, 1);
v___x_4708_ = lean_unsigned_to_nat(0u);
v___x_4709_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4707_, v___x_4708_);
lean_dec(v_a_4707_);
return v___x_4709_;
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
v_a_4710_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4706_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4706_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4718_; lean_object* v___x_4719_; 
v_mvarId_4718_ = lean_ctor_get(v_x_4699_, 0);
lean_inc(v_mvarId_4718_);
lean_dec_ref_known(v_x_4699_, 1);
v___x_4719_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4718_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref_known(v___x_4719_, 1);
v___x_4721_ = lean_unsigned_to_nat(0u);
v___x_4722_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4720_, v___x_4721_);
lean_dec(v_a_4720_);
return v___x_4722_;
}
else
{
lean_object* v_a_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4730_; 
v_a_4723_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4725_ = v___x_4719_;
v_isShared_4726_ = v_isSharedCheck_4730_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_a_4723_);
lean_dec(v___x_4719_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4730_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v___x_4728_; 
if (v_isShared_4726_ == 0)
{
v___x_4728_ = v___x_4725_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_a_4723_);
v___x_4728_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
return v___x_4728_;
}
}
}
}
case 3:
{
uint8_t v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
lean_dec_ref_known(v_x_4699_, 1);
v___x_4731_ = 1;
v___x_4732_ = lean_box(v___x_4731_);
v___x_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
return v___x_4733_;
}
case 4:
{
lean_object* v_declName_4734_; lean_object* v_us_4735_; lean_object* v___x_4736_; 
v_declName_4734_ = lean_ctor_get(v_x_4699_, 0);
lean_inc(v_declName_4734_);
v_us_4735_ = lean_ctor_get(v_x_4699_, 1);
lean_inc(v_us_4735_);
lean_dec_ref_known(v_x_4699_, 2);
v___x_4736_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4734_, v_us_4735_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v___x_4736_, 1);
v___x_4738_ = lean_unsigned_to_nat(0u);
v___x_4739_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4737_, v___x_4738_);
lean_dec(v_a_4737_);
return v___x_4739_;
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
v_a_4740_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4742_ = v___x_4736_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4736_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
case 5:
{
lean_object* v_fn_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v_fn_4748_ = lean_ctor_get(v_x_4699_, 0);
lean_inc_ref(v_fn_4748_);
lean_dec_ref_known(v_x_4699_, 2);
v___x_4749_ = lean_unsigned_to_nat(1u);
v___x_4750_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4748_, v___x_4749_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_);
return v___x_4750_;
}
case 6:
{
uint8_t v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
lean_dec_ref_known(v_x_4699_, 3);
v___x_4751_ = 0;
v___x_4752_ = lean_box(v___x_4751_);
v___x_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4752_);
return v___x_4753_;
}
case 7:
{
uint8_t v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; 
lean_dec_ref_known(v_x_4699_, 3);
v___x_4754_ = 1;
v___x_4755_ = lean_box(v___x_4754_);
v___x_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
return v___x_4756_;
}
case 8:
{
lean_object* v_body_4757_; 
v_body_4757_ = lean_ctor_get(v_x_4699_, 3);
lean_inc_ref(v_body_4757_);
lean_dec_ref_known(v_x_4699_, 4);
v_x_4699_ = v_body_4757_;
goto _start;
}
case 9:
{
uint8_t v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_dec_ref_known(v_x_4699_, 1);
v___x_4759_ = 0;
v___x_4760_ = lean_box(v___x_4759_);
v___x_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4760_);
return v___x_4761_;
}
case 10:
{
lean_object* v_expr_4762_; 
v_expr_4762_ = lean_ctor_get(v_x_4699_, 1);
lean_inc_ref(v_expr_4762_);
lean_dec_ref_known(v_x_4699_, 2);
v_x_4699_ = v_expr_4762_;
goto _start;
}
default: 
{
uint8_t v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
lean_dec_ref(v_x_4699_);
v___x_4764_ = 2;
v___x_4765_ = lean_box(v___x_4764_);
v___x_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
return v___x_4766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l_Lean_Meta_isTypeQuick(v_x_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v___x_4780_; 
lean_inc_ref(v_e_4774_);
v___x_4780_ = l_Lean_Meta_isTypeQuick(v_e_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4830_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4783_ = v___x_4780_;
v_isShared_4784_ = v_isSharedCheck_4830_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4780_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4830_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
uint8_t v___x_4785_; 
v___x_4785_ = lean_unbox(v_a_4781_);
lean_dec(v_a_4781_);
switch(v___x_4785_)
{
case 0:
{
uint8_t v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4789_; 
lean_dec_ref(v_e_4774_);
v___x_4786_ = 0;
v___x_4787_ = lean_box(v___x_4786_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 0, v___x_4787_);
v___x_4789_ = v___x_4783_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4787_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
case 1:
{
uint8_t v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4794_; 
lean_dec_ref(v_e_4774_);
v___x_4791_ = 1;
v___x_4792_ = lean_box(v___x_4791_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 0, v___x_4792_);
v___x_4794_ = v___x_4783_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4792_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
default: 
{
lean_object* v___x_4796_; 
lean_del_object(v___x_4783_);
lean_inc(v_a_4778_);
lean_inc_ref(v_a_4777_);
lean_inc(v_a_4776_);
lean_inc_ref(v_a_4775_);
v___x_4796_ = lean_infer_type(v_e_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4798_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
lean_inc(v_a_4797_);
lean_dec_ref_known(v___x_4796_, 1);
v___x_4798_ = l_Lean_Meta_whnfD(v_a_4797_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4813_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4801_ = v___x_4798_;
v_isShared_4802_ = v_isSharedCheck_4813_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4798_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4813_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
if (lean_obj_tag(v_a_4799_) == 3)
{
uint8_t v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4806_; 
lean_dec_ref_known(v_a_4799_, 1);
v___x_4803_ = 1;
v___x_4804_ = lean_box(v___x_4803_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v___x_4804_);
v___x_4806_ = v___x_4801_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
else
{
uint8_t v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4811_; 
lean_dec(v_a_4799_);
v___x_4808_ = 0;
v___x_4809_ = lean_box(v___x_4808_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v___x_4809_);
v___x_4811_ = v___x_4801_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4809_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
v_a_4814_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4798_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4798_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
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
v_a_4822_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4796_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4796_);
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
}
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
lean_dec_ref(v_e_4774_);
v_a_4831_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4780_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4780_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Lean_Meta_isType(v_e_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_);
lean_dec(v_a_4843_);
lean_dec_ref(v_a_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4846_){
_start:
{
switch(lean_obj_tag(v_x_4846_))
{
case 7:
{
lean_object* v_body_4847_; 
v_body_4847_ = lean_ctor_get(v_x_4846_, 2);
v_x_4846_ = v_body_4847_;
goto _start;
}
case 3:
{
lean_object* v_u_4849_; lean_object* v___x_4850_; 
v_u_4849_ = lean_ctor_get(v_x_4846_, 0);
lean_inc(v_u_4849_);
v___x_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4850_, 0, v_u_4849_);
return v___x_4850_;
}
default: 
{
lean_object* v___x_4851_; 
v___x_4851_ = lean_box(0);
return v___x_4851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4852_);
lean_dec_ref(v_x_4852_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4854_, lean_object* v_body_4855_, lean_object* v_x_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4854_, v_body_4855_, v_x_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4865_, lean_object* v_xs_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v_l_4873_; 
switch(lean_obj_tag(v_type_4865_))
{
case 3:
{
lean_object* v_u_4876_; 
lean_dec_ref(v_xs_4866_);
v_u_4876_ = lean_ctor_get(v_type_4865_, 0);
lean_inc(v_u_4876_);
lean_dec_ref_known(v_type_4865_, 1);
v_l_4873_ = v_u_4876_;
goto v___jp_4872_;
}
case 7:
{
lean_object* v_binderName_4877_; lean_object* v_binderType_4878_; lean_object* v_body_4879_; uint8_t v_binderInfo_4880_; lean_object* v___f_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v_binderName_4877_ = lean_ctor_get(v_type_4865_, 0);
lean_inc(v_binderName_4877_);
v_binderType_4878_ = lean_ctor_get(v_type_4865_, 1);
lean_inc_ref(v_binderType_4878_);
v_body_4879_ = lean_ctor_get(v_type_4865_, 2);
lean_inc_ref(v_body_4879_);
v_binderInfo_4880_ = lean_ctor_get_uint8(v_type_4865_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4865_, 3);
lean_inc_ref(v_xs_4866_);
v___f_4881_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4881_, 0, v_xs_4866_);
lean_closure_set(v___f_4881_, 1, v_body_4879_);
v___x_4882_ = lean_expr_instantiate_rev(v_binderType_4878_, v_xs_4866_);
lean_dec_ref(v_xs_4866_);
lean_dec_ref(v_binderType_4878_);
v___x_4883_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4877_, v_binderInfo_4880_, v___x_4882_, v___f_4881_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
return v___x_4883_;
}
default: 
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_expr_instantiate_rev(v_type_4865_, v_xs_4866_);
lean_dec_ref(v_xs_4866_);
lean_dec_ref(v_type_4865_);
v___x_4885_ = l_Lean_Meta_whnfD(v___x_4884_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4897_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4888_ = v___x_4885_;
v_isShared_4889_ = v_isSharedCheck_4897_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4897_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
switch(lean_obj_tag(v_a_4886_))
{
case 3:
{
lean_object* v_u_4890_; 
lean_del_object(v___x_4888_);
v_u_4890_ = lean_ctor_get(v_a_4886_, 0);
lean_inc(v_u_4890_);
lean_dec_ref_known(v_a_4886_, 1);
v_l_4873_ = v_u_4890_;
goto v___jp_4872_;
}
case 7:
{
lean_object* v___x_4891_; 
lean_del_object(v___x_4888_);
v___x_4891_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4865_ = v_a_4886_;
v_xs_4866_ = v___x_4891_;
goto _start;
}
default: 
{
lean_object* v___x_4893_; lean_object* v___x_4895_; 
lean_dec(v_a_4886_);
v___x_4893_ = lean_box(0);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 0, v___x_4893_);
v___x_4895_ = v___x_4888_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
v_a_4898_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4885_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4885_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
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
v___jp_4872_:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v_l_4873_);
v___x_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4874_);
return v___x_4875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4906_, lean_object* v_body_4907_, lean_object* v_x_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = lean_array_push(v_xs_4906_, v_x_4908_);
v___x_4915_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4907_, v___x_4914_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4916_, lean_object* v_xs_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4916_, v_xs_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_);
lean_dec(v_a_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v_a_4919_);
lean_dec_ref(v_a_4918_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4924_, lean_object* v_cache_4925_, lean_object* v_a_x3f_4926_){
_start:
{
lean_object* v___x_4928_; lean_object* v_mctx_4929_; lean_object* v_zetaDeltaFVarIds_4930_; lean_object* v_postponed_4931_; lean_object* v_diag_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4942_; 
v___x_4928_ = lean_st_ref_take(v_a_4924_);
v_mctx_4929_ = lean_ctor_get(v___x_4928_, 0);
v_zetaDeltaFVarIds_4930_ = lean_ctor_get(v___x_4928_, 2);
v_postponed_4931_ = lean_ctor_get(v___x_4928_, 3);
v_diag_4932_ = lean_ctor_get(v___x_4928_, 4);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4942_ == 0)
{
lean_object* v_unused_4943_; 
v_unused_4943_ = lean_ctor_get(v___x_4928_, 1);
lean_dec(v_unused_4943_);
v___x_4934_ = v___x_4928_;
v_isShared_4935_ = v_isSharedCheck_4942_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_diag_4932_);
lean_inc(v_postponed_4931_);
lean_inc(v_zetaDeltaFVarIds_4930_);
lean_inc(v_mctx_4929_);
lean_dec(v___x_4928_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4942_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4936_; lean_object* v___x_4938_; 
v___x_4936_ = lean_box(0);
if (v_isShared_4935_ == 0)
{
lean_ctor_set(v___x_4934_, 1, v_cache_4925_);
v___x_4938_ = v___x_4934_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_mctx_4929_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v_cache_4925_);
lean_ctor_set(v_reuseFailAlloc_4941_, 2, v_zetaDeltaFVarIds_4930_);
lean_ctor_set(v_reuseFailAlloc_4941_, 3, v_postponed_4931_);
lean_ctor_set(v_reuseFailAlloc_4941_, 4, v_diag_4932_);
v___x_4938_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = lean_st_ref_put(v_a_4924_, v___x_4938_);
v___x_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4936_);
return v___x_4940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4944_, lean_object* v_cache_4945_, lean_object* v_a_x3f_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4944_, v_cache_4945_, v_a_x3f_4946_);
lean_dec(v_a_x3f_4946_);
lean_dec(v_a_4944_);
return v_res_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4949_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v_cache_4958_; lean_object* v___x_4959_; 
v___x_4956_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4957_ = lean_st_ref_get(v_a_4951_);
v_cache_4958_ = lean_ctor_get(v___x_4957_, 1);
lean_inc_ref(v_cache_4958_);
lean_dec(v___x_4957_);
v___x_4959_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4949_, v___x_4956_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4976_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4962_ = v___x_4959_;
v_isShared_4963_ = v_isSharedCheck_4976_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4959_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4976_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
lean_inc(v_a_4960_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set_tag(v___x_4962_, 1);
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
lean_object* v___x_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
v___x_4966_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4951_, v_cache_4958_, v___x_4965_);
lean_dec_ref(v___x_4965_);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4973_ == 0)
{
lean_object* v_unused_4974_; 
v_unused_4974_ = lean_ctor_get(v___x_4966_, 0);
lean_dec(v_unused_4974_);
v___x_4968_ = v___x_4966_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_dec(v___x_4966_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v_a_4960_);
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4960_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4986_; 
v_a_4977_ = lean_ctor_get(v___x_4959_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4959_, 1);
v___x_4978_ = lean_box(0);
v___x_4979_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4951_, v_cache_4958_, v___x_4978_);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_4986_ == 0)
{
lean_object* v_unused_4987_; 
v_unused_4987_ = lean_ctor_get(v___x_4979_, 0);
lean_dec(v_unused_4987_);
v___x_4981_ = v___x_4979_;
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
else
{
lean_dec(v___x_4979_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4984_; 
if (v_isShared_4982_ == 0)
{
lean_ctor_set_tag(v___x_4981_, 1);
lean_ctor_set(v___x_4981_, 0, v_a_4977_);
v___x_4984_ = v___x_4981_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4977_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
else
{
lean_object* v___x_4988_; 
lean_dec_ref(v_type_4949_);
v___x_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4955_);
return v___x_4988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5017_; 
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5005_ = v___x_5002_;
v_isShared_5006_ = v_isSharedCheck_5017_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_5002_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5017_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
if (lean_obj_tag(v_a_5003_) == 0)
{
uint8_t v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5010_; 
v___x_5007_ = 0;
v___x_5008_ = lean_box(v___x_5007_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v___x_5008_);
v___x_5010_ = v___x_5005_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_5008_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
else
{
uint8_t v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5015_; 
lean_dec_ref_known(v_a_5003_, 1);
v___x_5012_ = 1;
v___x_5013_ = lean_box(v___x_5012_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v___x_5013_);
v___x_5015_ = v___x_5005_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
v_a_5018_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5002_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5002_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_Lean_Meta_isTypeFormerType(v_type_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
return v_res_5032_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5033_, lean_object* v_x_5034_){
_start:
{
if (lean_obj_tag(v_x_5033_) == 0)
{
if (lean_obj_tag(v_x_5034_) == 0)
{
uint8_t v___x_5035_; 
v___x_5035_ = 1;
return v___x_5035_;
}
else
{
uint8_t v___x_5036_; 
v___x_5036_ = 0;
return v___x_5036_;
}
}
else
{
if (lean_obj_tag(v_x_5034_) == 0)
{
uint8_t v___x_5037_; 
v___x_5037_ = 0;
return v___x_5037_;
}
else
{
lean_object* v_val_5038_; lean_object* v_val_5039_; uint8_t v___x_5040_; 
v_val_5038_ = lean_ctor_get(v_x_5033_, 0);
v_val_5039_ = lean_ctor_get(v_x_5034_, 0);
v___x_5040_ = lean_level_eq(v_val_5038_, v_val_5039_);
return v___x_5040_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5041_, lean_object* v_x_5042_){
_start:
{
uint8_t v_res_5043_; lean_object* v_r_5044_; 
v_res_5043_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5041_, v_x_5042_);
lean_dec(v_x_5042_);
lean_dec(v_x_5041_);
v_r_5044_ = lean_box(v_res_5043_);
return v_r_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v___x_5053_; 
v___x_5053_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5064_; 
v_a_5054_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5056_ = v___x_5053_;
v_isShared_5057_ = v_isSharedCheck_5064_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_5053_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5064_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5058_; uint8_t v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5058_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5059_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5054_, v___x_5058_);
lean_dec(v_a_5054_);
v___x_5060_ = lean_box(v___x_5059_);
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 0, v___x_5060_);
v___x_5062_ = v___x_5056_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
v_a_5065_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_5053_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_5053_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Lean_Meta_isPropFormerType(v_type_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
lean_dec(v_a_5077_);
lean_dec_ref(v_a_5076_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
return v_res_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v___x_5086_; 
lean_inc(v_a_5084_);
lean_inc_ref(v_a_5083_);
lean_inc(v_a_5082_);
lean_inc_ref(v_a_5081_);
v___x_5086_ = lean_infer_type(v_e_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; lean_object* v___x_5088_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5086_, 1);
v___x_5088_ = l_Lean_Meta_isTypeFormerType(v_a_5087_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_);
return v___x_5088_;
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
v_a_5089_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5086_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5086_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v_res_5103_; 
v_res_5103_ = l_Lean_Meta_isTypeFormer(v_e_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5104_, lean_object* v_maxFVars_x3f_5105_, lean_object* v_k_5106_, uint8_t v_cleanupAnnotations_5107_, uint8_t v_whnfType_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v___f_5114_; lean_object* v___x_5115_; 
v___f_5114_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5114_, 0, v_k_5106_);
v___x_5115_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5104_, v_maxFVars_x3f_5105_, v___f_5114_, v_cleanupAnnotations_5107_, v_whnfType_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
v_a_5116_ = lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5115_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5115_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
v_a_5124_ = lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_5115_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5115_);
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
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5132_, lean_object* v_maxFVars_x3f_5133_, lean_object* v_k_5134_, lean_object* v_cleanupAnnotations_5135_, lean_object* v_whnfType_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5142_; uint8_t v_whnfType_boxed_5143_; lean_object* v_res_5144_; 
v_cleanupAnnotations_boxed_5142_ = lean_unbox(v_cleanupAnnotations_5135_);
v_whnfType_boxed_5143_ = lean_unbox(v_whnfType_5136_);
v_res_5144_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5132_, v_maxFVars_x3f_5133_, v_k_5134_, v_cleanupAnnotations_boxed_5142_, v_whnfType_boxed_5143_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5145_, lean_object* v_type_5146_, lean_object* v_maxFVars_x3f_5147_, lean_object* v_k_5148_, uint8_t v_cleanupAnnotations_5149_, uint8_t v_whnfType_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v___x_5156_; 
v___x_5156_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5146_, v_maxFVars_x3f_5147_, v_k_5148_, v_cleanupAnnotations_5149_, v_whnfType_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
return v___x_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5157_, lean_object* v_type_5158_, lean_object* v_maxFVars_x3f_5159_, lean_object* v_k_5160_, lean_object* v_cleanupAnnotations_5161_, lean_object* v_whnfType_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5168_; uint8_t v_whnfType_boxed_5169_; lean_object* v_res_5170_; 
v_cleanupAnnotations_boxed_5168_ = lean_unbox(v_cleanupAnnotations_5161_);
v_whnfType_boxed_5169_ = lean_unbox(v_whnfType_5162_);
v_res_5170_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5157_, v_type_5158_, v_maxFVars_x3f_5159_, v_k_5160_, v_cleanupAnnotations_boxed_5168_, v_whnfType_boxed_5169_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
return v_res_5170_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5171_, lean_object* v_as_5172_, size_t v_i_5173_, size_t v_stop_5174_){
_start:
{
uint8_t v___x_5175_; 
v___x_5175_ = lean_usize_dec_eq(v_i_5173_, v_stop_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; uint8_t v___x_5177_; 
v___x_5176_ = lean_array_uget_borrowed(v_as_5172_, v_i_5173_);
v___x_5177_ = lean_expr_eqv(v_a_5171_, v___x_5176_);
if (v___x_5177_ == 0)
{
size_t v___x_5178_; size_t v___x_5179_; 
v___x_5178_ = ((size_t)1ULL);
v___x_5179_ = lean_usize_add(v_i_5173_, v___x_5178_);
v_i_5173_ = v___x_5179_;
goto _start;
}
else
{
return v___x_5177_;
}
}
else
{
uint8_t v___x_5181_; 
v___x_5181_ = 0;
return v___x_5181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5182_, lean_object* v_as_5183_, lean_object* v_i_5184_, lean_object* v_stop_5185_){
_start:
{
size_t v_i_boxed_5186_; size_t v_stop_boxed_5187_; uint8_t v_res_5188_; lean_object* v_r_5189_; 
v_i_boxed_5186_ = lean_unbox_usize(v_i_5184_);
lean_dec(v_i_5184_);
v_stop_boxed_5187_ = lean_unbox_usize(v_stop_5185_);
lean_dec(v_stop_5185_);
v_res_5188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5182_, v_as_5183_, v_i_boxed_5186_, v_stop_boxed_5187_);
lean_dec_ref(v_as_5183_);
lean_dec_ref(v_a_5182_);
v_r_5189_ = lean_box(v_res_5188_);
return v_r_5189_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v___x_5192_; lean_object* v___x_5193_; uint8_t v___x_5194_; 
v___x_5192_ = lean_unsigned_to_nat(0u);
v___x_5193_ = lean_array_get_size(v_as_5190_);
v___x_5194_ = lean_nat_dec_lt(v___x_5192_, v___x_5193_);
if (v___x_5194_ == 0)
{
return v___x_5194_;
}
else
{
size_t v___x_5195_; size_t v___x_5196_; uint8_t v___x_5197_; 
v___x_5195_ = ((size_t)0ULL);
v___x_5196_ = lean_usize_of_nat(v___x_5193_);
v___x_5197_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5191_, v_as_5190_, v___x_5195_, v___x_5196_);
return v___x_5197_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5198_, lean_object* v_a_5199_){
_start:
{
uint8_t v_res_5200_; lean_object* v_r_5201_; 
v_res_5200_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5198_, v_a_5199_);
lean_dec_ref(v_a_5199_);
lean_dec_ref(v_as_5198_);
v_r_5201_ = lean_box(v_res_5200_);
return v_r_5201_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5202_, lean_object* v_e_5203_){
_start:
{
uint8_t v___x_5204_; lean_object* v_d_5206_; lean_object* v_b_5207_; 
v___x_5204_ = l_Lean_Expr_hasFVar(v_e_5203_);
if (v___x_5204_ == 0)
{
lean_dec_ref(v_e_5203_);
return v___x_5204_;
}
else
{
switch(lean_obj_tag(v_e_5203_))
{
case 7:
{
lean_object* v_binderType_5210_; lean_object* v_body_5211_; 
v_binderType_5210_ = lean_ctor_get(v_e_5203_, 1);
lean_inc_ref(v_binderType_5210_);
v_body_5211_ = lean_ctor_get(v_e_5203_, 2);
lean_inc_ref(v_body_5211_);
lean_dec_ref_known(v_e_5203_, 3);
v_d_5206_ = v_binderType_5210_;
v_b_5207_ = v_body_5211_;
goto v___jp_5205_;
}
case 6:
{
lean_object* v_binderType_5212_; lean_object* v_body_5213_; 
v_binderType_5212_ = lean_ctor_get(v_e_5203_, 1);
lean_inc_ref(v_binderType_5212_);
v_body_5213_ = lean_ctor_get(v_e_5203_, 2);
lean_inc_ref(v_body_5213_);
lean_dec_ref_known(v_e_5203_, 3);
v_d_5206_ = v_binderType_5212_;
v_b_5207_ = v_body_5213_;
goto v___jp_5205_;
}
case 10:
{
lean_object* v_expr_5214_; 
v_expr_5214_ = lean_ctor_get(v_e_5203_, 1);
lean_inc_ref(v_expr_5214_);
lean_dec_ref_known(v_e_5203_, 2);
v_e_5203_ = v_expr_5214_;
goto _start;
}
case 8:
{
lean_object* v_type_5216_; lean_object* v_value_5217_; lean_object* v_body_5218_; uint8_t v___x_5219_; 
v_type_5216_ = lean_ctor_get(v_e_5203_, 1);
lean_inc_ref(v_type_5216_);
v_value_5217_ = lean_ctor_get(v_e_5203_, 2);
lean_inc_ref(v_value_5217_);
v_body_5218_ = lean_ctor_get(v_e_5203_, 3);
lean_inc_ref(v_body_5218_);
lean_dec_ref_known(v_e_5203_, 4);
v___x_5219_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5202_, v_type_5216_);
if (v___x_5219_ == 0)
{
uint8_t v___x_5220_; 
v___x_5220_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5202_, v_value_5217_);
if (v___x_5220_ == 0)
{
v_e_5203_ = v_body_5218_;
goto _start;
}
else
{
lean_dec_ref(v_body_5218_);
return v___x_5204_;
}
}
else
{
lean_dec_ref(v_body_5218_);
lean_dec_ref(v_value_5217_);
return v___x_5204_;
}
}
case 5:
{
lean_object* v_fn_5222_; lean_object* v_arg_5223_; uint8_t v___x_5224_; 
v_fn_5222_ = lean_ctor_get(v_e_5203_, 0);
lean_inc_ref(v_fn_5222_);
v_arg_5223_ = lean_ctor_get(v_e_5203_, 1);
lean_inc_ref(v_arg_5223_);
lean_dec_ref_known(v_e_5203_, 2);
v___x_5224_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5202_, v_fn_5222_);
if (v___x_5224_ == 0)
{
v_e_5203_ = v_arg_5223_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5223_);
return v___x_5204_;
}
}
case 11:
{
lean_object* v_struct_5226_; 
v_struct_5226_ = lean_ctor_get(v_e_5203_, 2);
lean_inc_ref(v_struct_5226_);
lean_dec_ref_known(v_e_5203_, 3);
v_e_5203_ = v_struct_5226_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5228_; lean_object* v___x_5229_; uint8_t v___x_5230_; 
v_fvarId_5228_ = lean_ctor_get(v_e_5203_, 0);
lean_inc(v_fvarId_5228_);
lean_dec_ref_known(v_e_5203_, 1);
v___x_5229_ = l_Lean_Expr_fvar___override(v_fvarId_5228_);
v___x_5230_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5202_, v___x_5229_);
lean_dec_ref(v___x_5229_);
return v___x_5230_;
}
default: 
{
uint8_t v___x_5231_; 
lean_dec_ref(v_e_5203_);
v___x_5231_ = 0;
return v___x_5231_;
}
}
}
v___jp_5205_:
{
uint8_t v___x_5208_; 
v___x_5208_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5202_, v_d_5206_);
if (v___x_5208_ == 0)
{
v_e_5203_ = v_b_5207_;
goto _start;
}
else
{
lean_dec_ref(v_b_5207_);
return v___x_5204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5232_, lean_object* v_e_5233_){
_start:
{
uint8_t v_res_5234_; lean_object* v_r_5235_; 
v_res_5234_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5232_, v_e_5233_);
lean_dec_ref(v_xs_5232_);
v_r_5235_ = lean_box(v_res_5234_);
return v_r_5235_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5238_ = l_Lean_stringToMessageData(v___x_5237_);
return v___x_5238_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5240_; lean_object* v___x_5241_; 
v___x_5240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5241_ = l_Lean_stringToMessageData(v___x_5240_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5242_, lean_object* v_type_5243_, lean_object* v_as_5244_, size_t v_sz_5245_, size_t v_i_5246_, lean_object* v_b_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_a_5254_; uint8_t v___x_5258_; 
v___x_5258_ = lean_usize_dec_lt(v_i_5246_, v_sz_5245_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
lean_dec_ref(v_type_5243_);
v___x_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5259_, 0, v_b_5247_);
return v___x_5259_;
}
else
{
lean_object* v___x_5260_; lean_object* v_a_5261_; uint8_t v___x_5262_; 
v___x_5260_ = lean_box(0);
v_a_5261_ = lean_array_uget_borrowed(v_as_5244_, v_i_5246_);
lean_inc(v_a_5261_);
v___x_5262_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5242_, v_a_5261_);
if (v___x_5262_ == 0)
{
v_a_5254_ = v___x_5260_;
goto v___jp_5253_;
}
else
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___x_5263_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5261_);
v___x_5264_ = l_Lean_MessageData_ofExpr(v_a_5261_);
v___x_5265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5263_);
lean_ctor_set(v___x_5265_, 1, v___x_5264_);
v___x_5266_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5267_, 0, v___x_5265_);
lean_ctor_set(v___x_5267_, 1, v___x_5266_);
lean_inc_ref(v_type_5243_);
v___x_5268_ = l_Lean_MessageData_ofExpr(v_type_5243_);
v___x_5269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5267_);
lean_ctor_set(v___x_5269_, 1, v___x_5268_);
v___x_5270_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5269_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_);
if (lean_obj_tag(v___x_5270_) == 0)
{
lean_dec_ref_known(v___x_5270_, 1);
v_a_5254_ = v___x_5260_;
goto v___jp_5253_;
}
else
{
lean_dec_ref(v_type_5243_);
return v___x_5270_;
}
}
}
v___jp_5253_:
{
size_t v___x_5255_; size_t v___x_5256_; 
v___x_5255_ = ((size_t)1ULL);
v___x_5256_ = lean_usize_add(v_i_5246_, v___x_5255_);
v_i_5246_ = v___x_5256_;
v_b_5247_ = v_a_5254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5271_, lean_object* v_type_5272_, lean_object* v_as_5273_, lean_object* v_sz_5274_, lean_object* v_i_5275_, lean_object* v_b_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_){
_start:
{
size_t v_sz_boxed_5282_; size_t v_i_boxed_5283_; lean_object* v_res_5284_; 
v_sz_boxed_5282_ = lean_unbox_usize(v_sz_5274_);
lean_dec(v_sz_5274_);
v_i_boxed_5283_ = lean_unbox_usize(v_i_5275_);
lean_dec(v_i_5275_);
v_res_5284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5271_, v_type_5272_, v_as_5273_, v_sz_boxed_5282_, v_i_boxed_5283_, v_b_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec_ref(v_as_5273_);
lean_dec_ref(v_xs_5271_);
return v_res_5284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5285_, size_t v_i_5286_, lean_object* v_bs_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
uint8_t v___x_5293_; 
v___x_5293_ = lean_usize_dec_lt(v_i_5286_, v_sz_5285_);
if (v___x_5293_ == 0)
{
lean_object* v___x_5294_; 
v___x_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5294_, 0, v_bs_5287_);
return v___x_5294_;
}
else
{
lean_object* v_v_5295_; lean_object* v___x_5296_; lean_object* v_bs_x27_5297_; lean_object* v___x_5298_; 
v_v_5295_ = lean_array_uget(v_bs_5287_, v_i_5286_);
v___x_5296_ = lean_unsigned_to_nat(0u);
v_bs_x27_5297_ = lean_array_uset(v_bs_5287_, v_i_5286_, v___x_5296_);
lean_inc(v___y_5291_);
lean_inc_ref(v___y_5290_);
lean_inc(v___y_5289_);
lean_inc_ref(v___y_5288_);
v___x_5298_ = lean_infer_type(v_v_5295_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_);
if (lean_obj_tag(v___x_5298_) == 0)
{
lean_object* v_a_5299_; size_t v___x_5300_; size_t v___x_5301_; lean_object* v___x_5302_; 
v_a_5299_ = lean_ctor_get(v___x_5298_, 0);
lean_inc(v_a_5299_);
lean_dec_ref_known(v___x_5298_, 1);
v___x_5300_ = ((size_t)1ULL);
v___x_5301_ = lean_usize_add(v_i_5286_, v___x_5300_);
v___x_5302_ = lean_array_uset(v_bs_x27_5297_, v_i_5286_, v_a_5299_);
v_i_5286_ = v___x_5301_;
v_bs_5287_ = v___x_5302_;
goto _start;
}
else
{
lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5311_; 
lean_dec_ref(v_bs_x27_5297_);
v_a_5304_ = lean_ctor_get(v___x_5298_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5298_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5306_ = v___x_5298_;
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_dec(v___x_5298_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5309_; 
if (v_isShared_5307_ == 0)
{
v___x_5309_ = v___x_5306_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5312_, lean_object* v_i_5313_, lean_object* v_bs_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
size_t v_sz_boxed_5320_; size_t v_i_boxed_5321_; lean_object* v_res_5322_; 
v_sz_boxed_5320_ = lean_unbox_usize(v_sz_5312_);
lean_dec(v_sz_5312_);
v_i_boxed_5321_ = lean_unbox_usize(v_i_5313_);
lean_dec(v_i_5313_);
v_res_5322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5320_, v_i_boxed_5321_, v_bs_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v___y_5316_);
lean_dec_ref(v___y_5315_);
return v_res_5322_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5324_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5325_ = l_Lean_stringToMessageData(v___x_5324_);
return v___x_5325_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5327_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5328_ = l_Lean_stringToMessageData(v___x_5327_);
return v___x_5328_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5330_; lean_object* v___x_5331_; 
v___x_5330_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5331_ = l_Lean_stringToMessageData(v___x_5330_);
return v___x_5331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5332_, lean_object* v_n_5333_, lean_object* v_xs_5334_, lean_object* v_x_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
lean_object* v___x_5365_; uint8_t v___x_5366_; 
v___x_5365_ = lean_array_get_size(v_xs_5334_);
v___x_5366_ = lean_nat_dec_eq(v___x_5365_, v_n_5333_);
if (v___x_5366_ == 0)
{
lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v_a_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5386_; 
lean_dec_ref(v_xs_5334_);
v___x_5367_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5368_ = l_Lean_MessageData_ofExpr(v_type_5332_);
v___x_5369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5367_);
lean_ctor_set(v___x_5369_, 1, v___x_5368_);
v___x_5370_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5371_, 0, v___x_5369_);
lean_ctor_set(v___x_5371_, 1, v___x_5370_);
v___x_5372_ = l_Nat_reprFast(v_n_5333_);
v___x_5373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5373_, 0, v___x_5372_);
v___x_5374_ = l_Lean_MessageData_ofFormat(v___x_5373_);
v___x_5375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5371_);
lean_ctor_set(v___x_5375_, 1, v___x_5374_);
v___x_5376_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5377_, 0, v___x_5375_);
lean_ctor_set(v___x_5377_, 1, v___x_5376_);
v___x_5378_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5377_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
v_a_5379_ = lean_ctor_get(v___x_5378_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5378_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5381_ = v___x_5378_;
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_a_5379_);
lean_dec(v___x_5378_);
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
else
{
lean_dec(v_n_5333_);
goto v___jp_5341_;
}
v___jp_5341_:
{
size_t v_sz_5342_; size_t v___x_5343_; lean_object* v___x_5344_; 
v_sz_5342_ = lean_array_size(v_xs_5334_);
v___x_5343_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5334_);
v___x_5344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5342_, v___x_5343_, v_xs_5334_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_a_5345_; lean_object* v___x_5346_; size_t v_sz_5347_; lean_object* v___x_5348_; 
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
lean_inc(v_a_5345_);
lean_dec_ref_known(v___x_5344_, 1);
v___x_5346_ = lean_box(0);
v_sz_5347_ = lean_array_size(v_a_5345_);
v___x_5348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5334_, v_type_5332_, v_a_5345_, v_sz_5347_, v___x_5343_, v___x_5346_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
lean_dec_ref(v_xs_5334_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5355_; 
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5355_ == 0)
{
lean_object* v_unused_5356_; 
v_unused_5356_ = lean_ctor_get(v___x_5348_, 0);
lean_dec(v_unused_5356_);
v___x_5350_ = v___x_5348_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_dec(v___x_5348_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 0, v_a_5345_);
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5345_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec(v_a_5345_);
v_a_5357_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5348_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5348_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5334_);
lean_dec_ref(v_type_5332_);
return v___x_5344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5387_, lean_object* v_n_5388_, lean_object* v_xs_5389_, lean_object* v_x_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5387_, v_n_5388_, v_xs_5389_, v_x_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec_ref(v_x_5390_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5397_, lean_object* v_type_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v___f_5404_; lean_object* v___x_5405_; uint8_t v___x_5406_; lean_object* v___x_5407_; 
lean_inc(v_n_5397_);
lean_inc_ref(v_type_5398_);
v___f_5404_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5404_, 0, v_type_5398_);
lean_closure_set(v___f_5404_, 1, v_n_5397_);
v___x_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5405_, 0, v_n_5397_);
v___x_5406_ = 0;
v___x_5407_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5398_, v___x_5405_, v___f_5404_, v___x_5406_, v___x_5406_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5408_, lean_object* v_type_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v_res_5415_; 
v_res_5415_ = l_Lean_Meta_arrowDomainsN(v_n_5408_, v_type_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_);
lean_dec(v_a_5413_);
lean_dec_ref(v_a_5412_);
lean_dec(v_a_5411_);
lean_dec_ref(v_a_5410_);
return v_res_5415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5416_, lean_object* v_e_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_){
_start:
{
lean_object* v___x_5423_; 
lean_inc(v_a_5421_);
lean_inc_ref(v_a_5420_);
lean_inc(v_a_5419_);
lean_inc_ref(v_a_5418_);
v___x_5423_ = lean_infer_type(v_e_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5425_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
lean_inc(v_a_5424_);
lean_dec_ref_known(v___x_5423_, 1);
v___x_5425_ = l_Lean_Meta_arrowDomainsN(v_n_5416_, v_a_5424_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_);
return v___x_5425_;
}
else
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5433_; 
lean_dec(v_n_5416_);
v_a_5426_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5428_ = v___x_5423_;
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5423_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5433_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5431_; 
if (v_isShared_5429_ == 0)
{
v___x_5431_ = v___x_5428_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_a_5426_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
return v___x_5431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5434_, lean_object* v_e_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Lean_Meta_inferArgumentTypesN(v_n_5434_, v_e_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_);
lean_dec(v_a_5439_);
lean_dec_ref(v_a_5438_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
return v_res_5441_;
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
