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
lean_ctor_set(v___x_982_, 10, v___x_979_);
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
size_t v_x_1151__boxed_1843_; size_t v_x_1152__boxed_1844_; lean_object* v_res_1845_; 
v_x_1151__boxed_1843_ = lean_unbox_usize(v_x_1839_);
lean_dec(v_x_1839_);
v_x_1152__boxed_1844_ = lean_unbox_usize(v_x_1840_);
lean_dec(v_x_1840_);
v_res_1845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1838_, v_x_1151__boxed_1843_, v_x_1152__boxed_1844_, v_x_1841_, v_x_1842_);
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
lean_object* v___x_1857_; lean_object* v_mctx_1858_; lean_object* v_cache_1859_; lean_object* v_zetaDeltaFVarIds_1860_; lean_object* v_postponed_1861_; lean_object* v_diag_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1891_; 
v___x_1857_ = lean_st_ref_take(v___y_1855_);
v_mctx_1858_ = lean_ctor_get(v___x_1857_, 0);
v_cache_1859_ = lean_ctor_get(v___x_1857_, 1);
v_zetaDeltaFVarIds_1860_ = lean_ctor_get(v___x_1857_, 2);
v_postponed_1861_ = lean_ctor_get(v___x_1857_, 3);
v_diag_1862_ = lean_ctor_get(v___x_1857_, 4);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1864_ = v___x_1857_;
v_isShared_1865_ = v_isSharedCheck_1891_;
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
v_isShared_1865_ = v_isSharedCheck_1891_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_depth_1866_; lean_object* v_levelAssignDepth_1867_; lean_object* v_lmvarCounter_1868_; lean_object* v_mvarCounter_1869_; lean_object* v_lDecls_1870_; lean_object* v_decls_1871_; lean_object* v_userNames_1872_; lean_object* v_lAssignment_1873_; lean_object* v_eAssignment_1874_; lean_object* v_dAssignment_1875_; lean_object* v_synthNormMemo_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1890_; 
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
v_synthNormMemo_1876_ = lean_ctor_get(v_mctx_1858_, 10);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_mctx_1858_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1878_ = v_mctx_1858_;
v_isShared_1879_ = v_isSharedCheck_1890_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_synthNormMemo_1876_);
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
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1890_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1874_, v_mvarId_1853_, v_val_1854_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 8, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_depth_1866_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_levelAssignDepth_1867_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_lmvarCounter_1868_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_mvarCounter_1869_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v_lDecls_1870_);
lean_ctor_set(v_reuseFailAlloc_1889_, 5, v_decls_1871_);
lean_ctor_set(v_reuseFailAlloc_1889_, 6, v_userNames_1872_);
lean_ctor_set(v_reuseFailAlloc_1889_, 7, v_lAssignment_1873_);
lean_ctor_set(v_reuseFailAlloc_1889_, 8, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1889_, 9, v_dAssignment_1875_);
lean_ctor_set(v_reuseFailAlloc_1889_, 10, v_synthNormMemo_1876_);
v___x_1883_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1883_);
v___x_1885_ = v___x_1864_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_cache_1859_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_zetaDeltaFVarIds_1860_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_postponed_1861_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_diag_1862_);
v___x_1885_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_st_ref_put(v___y_1855_, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1880_);
return v___x_1887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1892_, lean_object* v_val_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1892_, v_val_1893_, v___y_1894_);
lean_dec(v___y_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1903_; 
lean_inc(v_a_1901_);
lean_inc_ref(v_a_1900_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc_ref(v_type_1897_);
v___x_1903_ = lean_infer_type(v_type_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = l_Lean_Meta_whnfD(v_a_1904_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1940_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1940_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1940_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
switch(lean_obj_tag(v_a_1906_))
{
case 3:
{
lean_object* v_u_1910_; lean_object* v___x_1912_; 
lean_dec_ref(v_type_1897_);
v_u_1910_ = lean_ctor_get(v_a_1906_, 0);
lean_inc(v_u_1910_);
lean_dec_ref_known(v_a_1906_, 1);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v_u_1910_);
v___x_1912_ = v___x_1908_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_u_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
case 2:
{
lean_object* v_mvarId_1914_; lean_object* v___x_1915_; 
lean_del_object(v___x_1908_);
v_mvarId_1914_ = lean_ctor_get(v_a_1906_, 0);
lean_inc_n(v_mvarId_1914_, 2);
lean_dec_ref_known(v_a_1906_, 1);
v___x_1915_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1914_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; uint8_t v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = lean_unbox(v_a_1916_);
lean_dec(v_a_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref(v_type_1897_);
v___x_1918_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_n(v_a_1919_, 2);
lean_dec_ref_known(v___x_1918_, 1);
v___x_1920_ = l_Lean_mkSort(v_a_1919_);
v___x_1921_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1914_, v___x_1920_, v_a_1899_);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1921_, 0);
lean_dec(v_unused_1929_);
v___x_1923_ = v___x_1921_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_dec(v___x_1921_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v_a_1919_);
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1919_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_dec(v_mvarId_1914_);
return v___x_1918_;
}
}
else
{
lean_object* v___x_1930_; 
lean_dec(v_mvarId_1914_);
v___x_1930_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_1930_;
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_mvarId_1914_);
lean_dec_ref(v_type_1897_);
v_a_1931_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1915_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1915_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
default: 
{
lean_object* v___x_1939_; 
lean_del_object(v___x_1908_);
lean_dec(v_a_1906_);
v___x_1939_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_type_1897_);
v_a_1941_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1905_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1905_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_type_1897_);
v_a_1949_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1903_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1903_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Meta_getLevel(v_type_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1964_, lean_object* v_val_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1964_, v_val_1965_, v___y_1967_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1972_, lean_object* v_val_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1972_, v_val_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1981_, v_x_1982_, v_x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1985_, lean_object* v_x_1986_, size_t v_x_1987_, size_t v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1986_, v_x_1987_, v_x_1988_, v_x_1989_, v_x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
size_t v_x_1500__boxed_1998_; size_t v_x_1501__boxed_1999_; lean_object* v_res_2000_; 
v_x_1500__boxed_1998_ = lean_unbox_usize(v_x_1994_);
lean_dec(v_x_1994_);
v_x_1501__boxed_1999_ = lean_unbox_usize(v_x_1995_);
lean_dec(v_x_1995_);
v_res_2000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_1992_, v_x_1993_, v_x_1500__boxed_1998_, v_x_1501__boxed_1999_, v_x_1996_, v_x_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2001_, lean_object* v_n_2002_, lean_object* v_k_2003_, lean_object* v_v_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2002_, v_k_2003_, v_v_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2006_, size_t v_depth_2007_, lean_object* v_keys_2008_, lean_object* v_vals_2009_, lean_object* v_heq_2010_, lean_object* v_i_2011_, lean_object* v_entries_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2007_, v_keys_2008_, v_vals_2009_, v_i_2011_, v_entries_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2014_, lean_object* v_depth_2015_, lean_object* v_keys_2016_, lean_object* v_vals_2017_, lean_object* v_heq_2018_, lean_object* v_i_2019_, lean_object* v_entries_2020_){
_start:
{
size_t v_depth_boxed_2021_; lean_object* v_res_2022_; 
v_depth_boxed_2021_ = lean_unbox_usize(v_depth_2015_);
lean_dec(v_depth_2015_);
v_res_2022_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2014_, v_depth_boxed_2021_, v_keys_2016_, v_vals_2017_, v_heq_2018_, v_i_2019_, v_entries_2020_);
lean_dec_ref(v_vals_2017_);
lean_dec_ref(v_keys_2016_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2024_, v_x_2025_, v_x_2026_, v_x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2029_, lean_object* v_b_2030_, lean_object* v_c_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; 
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
v___x_2037_ = lean_apply_7(v_k_2029_, v_b_2030_, v_c_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, lean_box(0));
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2038_, lean_object* v_b_2039_, lean_object* v_c_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2038_, v_b_2039_, v_c_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2047_, lean_object* v_k_2048_, uint8_t v_cleanupAnnotations_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___f_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___f_2055_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2055_, 0, v_k_2048_);
v___x_2056_ = 0;
v___x_2057_ = lean_box(0);
v___x_2058_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2056_, v___x_2057_, v_type_2047_, v___f_2055_, v_cleanupAnnotations_2049_, v___x_2056_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2058_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2058_);
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
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2075_, lean_object* v_k_2076_, lean_object* v_cleanupAnnotations_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2083_; lean_object* v_res_2084_; 
v_cleanupAnnotations_boxed_2083_ = lean_unbox(v_cleanupAnnotations_2077_);
v_res_2084_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2075_, v_k_2076_, v_cleanupAnnotations_boxed_2083_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2085_, lean_object* v_type_2086_, lean_object* v_k_2087_, uint8_t v_cleanupAnnotations_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2086_, v_k_2087_, v_cleanupAnnotations_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2095_, lean_object* v_type_2096_, lean_object* v_k_2097_, lean_object* v_cleanupAnnotations_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2104_; lean_object* v_res_2105_; 
v_cleanupAnnotations_boxed_2104_ = lean_unbox(v_cleanupAnnotations_2098_);
v_res_2105_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2095_, v_type_2096_, v_k_2097_, v_cleanupAnnotations_boxed_2104_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2106_, size_t v_i_2107_, size_t v_stop_2108_, lean_object* v_b_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_usize_dec_eq(v_i_2107_, v_stop_2108_);
if (v___x_2115_ == 0)
{
size_t v___x_2116_; size_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = lean_usize_sub(v_i_2107_, v___x_2116_);
v___x_2118_ = lean_array_uget_borrowed(v_as_2106_, v___x_2117_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
lean_inc(v___x_2118_);
v___x_2119_ = lean_infer_type(v___x_2118_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v___x_2121_ = l_Lean_Meta_getLevel(v_a_2120_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = l_Lean_mkLevelIMax_x27(v_a_2122_, v_b_2109_);
v_i_2107_ = v___x_2117_;
v_b_2109_ = v___x_2123_;
goto _start;
}
else
{
lean_dec(v_b_2109_);
return v___x_2121_;
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_b_2109_);
v_a_2125_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2119_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2119_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_b_2109_);
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2134_, lean_object* v_i_2135_, lean_object* v_stop_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
size_t v_i_boxed_2143_; size_t v_stop_boxed_2144_; lean_object* v_res_2145_; 
v_i_boxed_2143_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_stop_boxed_2144_ = lean_unbox_usize(v_stop_2136_);
lean_dec(v_stop_2136_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2134_, v_i_boxed_2143_, v_stop_boxed_2144_, v_b_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v_as_2134_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2146_, lean_object* v_e_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_a_2154_; lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_Meta_getLevel(v_e_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2160_ = lean_array_get_size(v_xs_2146_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = lean_nat_dec_lt(v___x_2161_, v___x_2160_);
if (v___x_2162_ == 0)
{
v_a_2154_ = v_a_2159_;
goto v___jp_2153_;
}
else
{
size_t v___x_2163_; size_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_usize_of_nat(v___x_2160_);
v___x_2164_ = ((size_t)0ULL);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2146_, v___x_2163_, v___x_2164_, v_a_2159_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v_a_2154_ = v_a_2166_;
goto v___jp_2153_;
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
v_a_2167_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2165_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2165_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
v_a_2175_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2158_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2158_);
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
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = l_Lean_Level_normalize(v_a_2154_);
lean_dec(v_a_2154_);
v___x_2156_ = l_Lean_mkSort(v___x_2155_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2183_, lean_object* v_e_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2183_, v_e_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec_ref(v_xs_2183_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___f_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; 
v___f_2198_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2199_ = 0;
v___x_2200_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2192_, v___f_2198_, v___x_2199_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2208_, lean_object* v_k_2209_, uint8_t v_cleanupAnnotations_2210_, uint8_t v_preserveNondepLet_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___f_2217_; uint8_t v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2217_, 0, v_k_2209_);
v___x_2218_ = 1;
v___x_2219_ = 0;
v___x_2220_ = lean_box(0);
v___x_2221_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2208_, v___x_2218_, v___x_2218_, v_preserveNondepLet_2211_, v___x_2219_, v___x_2220_, v___f_2217_, v_cleanupAnnotations_2210_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
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
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2221_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2221_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2238_, lean_object* v_k_2239_, lean_object* v_cleanupAnnotations_2240_, lean_object* v_preserveNondepLet_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2247_; uint8_t v_preserveNondepLet_boxed_2248_; lean_object* v_res_2249_; 
v_cleanupAnnotations_boxed_2247_ = lean_unbox(v_cleanupAnnotations_2240_);
v_preserveNondepLet_boxed_2248_ = lean_unbox(v_preserveNondepLet_2241_);
v_res_2249_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2238_, v_k_2239_, v_cleanupAnnotations_boxed_2247_, v_preserveNondepLet_boxed_2248_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2250_, lean_object* v_e_2251_, lean_object* v_k_2252_, uint8_t v_cleanupAnnotations_2253_, uint8_t v_preserveNondepLet_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2251_, v_k_2252_, v_cleanupAnnotations_2253_, v_preserveNondepLet_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2261_, lean_object* v_e_2262_, lean_object* v_k_2263_, lean_object* v_cleanupAnnotations_2264_, lean_object* v_preserveNondepLet_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2271_; uint8_t v_preserveNondepLet_boxed_2272_; lean_object* v_res_2273_; 
v_cleanupAnnotations_boxed_2271_ = lean_unbox(v_cleanupAnnotations_2264_);
v_preserveNondepLet_boxed_2272_ = lean_unbox(v_preserveNondepLet_2265_);
v_res_2273_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2261_, v_e_2262_, v_k_2263_, v_cleanupAnnotations_boxed_2271_, v_preserveNondepLet_boxed_2272_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2274_, lean_object* v_e_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
v___x_2281_ = lean_infer_type(v_e_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; uint8_t v___x_2283_; uint8_t v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = 0;
v___x_2284_ = 1;
v___x_2285_ = 1;
v___x_2286_ = l_Lean_Meta_mkForallFVars(v_xs_2274_, v_a_2282_, v___x_2283_, v___x_2284_, v___x_2283_, v___x_2285_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2286_;
}
else
{
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2287_, lean_object* v_e_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2287_, v_e_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_xs_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___f_2302_; uint8_t v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; 
v___f_2302_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2303_ = 0;
v___x_2304_ = 1;
v___x_2305_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2296_, v___f_2302_, v___x_2303_, v___x_2304_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2312_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2318_ = l_Lean_stringToMessageData(v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2325_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2326_ = l_Lean_MessageData_ofName(v_mvarId_2319_);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2329_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2338_, lean_object* v_mvarId_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2346_, lean_object* v_mvarId_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2346_, v_mvarId_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v_mctx_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_st_ref_get(v_a_2356_);
v_mctx_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc_ref(v_mctx_2361_);
lean_dec(v___x_2360_);
v___x_2362_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2361_, v_mvarId_2354_);
lean_dec_ref(v_mctx_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
return v___x_2363_;
}
else
{
lean_object* v_val_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_mvarId_2354_);
v_val_2364_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2366_ = v___x_2362_;
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_val_2364_);
lean_dec(v___x_2362_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_type_2368_; lean_object* v___x_2370_; 
v_type_2368_ = lean_ctor_get(v_val_2364_, 2);
lean_inc_ref(v_type_2368_);
lean_dec(v_val_2364_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 0);
lean_ctor_set(v___x_2366_, 0, v_type_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_type_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_lctx_2385_; lean_object* v___x_2386_; 
v_lctx_2385_ = lean_ctor_get(v_a_2381_, 2);
lean_inc(v_fvarId_2380_);
lean_inc_ref(v_lctx_2385_);
v___x_2386_ = lean_local_ctx_find(v_lctx_2385_, v_fvarId_2380_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2380_, v_a_2382_, v_a_2383_);
return v___x_2387_;
}
else
{
lean_object* v_val_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_fvarId_2380_);
v_val_2388_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2390_ = v___x_2386_;
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_val_2388_);
lean_dec(v___x_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = l_Lean_LocalDecl_type(v_val_2388_);
lean_dec(v_val_2388_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2392_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2403_, v_a_2404_, v_a_2406_, v_a_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
return v_res_2416_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_instMonadEIO___redArg();
return v___x_2417_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2419_ = l_StateRefT_x27_instMonad___redArg(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_instMonadExceptOfEIO___redArg();
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___f_2424_; 
v___x_2423_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2424_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2424_, 0, v___x_2423_);
return v___f_2424_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___f_2426_; 
v___x_2425_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2426_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2426_, 0, v___x_2425_);
return v___f_2426_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; 
v___f_2427_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2428_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___f_2428_);
lean_ctor_set(v___x_2429_, 1, v___f_2427_);
return v___x_2429_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___f_2431_; 
v___x_2430_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2431_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2431_, 0, v___x_2430_);
return v___f_2431_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___f_2433_; 
v___x_2432_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2433_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2433_, 0, v___x_2432_);
return v___f_2433_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; 
v___f_2434_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2435_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___f_2435_);
lean_ctor_set(v___x_2436_, 1, v___f_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2439_, lean_object* v_inferType_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
uint8_t v_cacheInferType_2485_; 
v_cacheInferType_2485_ = lean_ctor_get_uint8(v_a_2441_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2485_ == 0)
{
lean_dec_ref(v_e_2439_);
goto v___jp_2446_;
}
else
{
uint8_t v___x_2486_; 
v___x_2486_ = l_Lean_Expr_hasMVar(v_e_2439_);
if (v___x_2486_ == 0)
{
lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___f_2487_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2489_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2439_, v_a_2441_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2587_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2587_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2587_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2534_; lean_object* v_cache_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2582_; 
v___x_2534_ = lean_st_ref_get(v_a_2442_);
v_cache_2535_ = lean_ctor_get(v___x_2534_, 1);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; 
v_unused_2583_ = lean_ctor_get(v___x_2534_, 4);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v___x_2534_, 3);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v___x_2534_, 2);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v___x_2534_, 0);
lean_dec(v_unused_2586_);
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2582_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_cache_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2582_;
goto v_resetjp_2536_;
}
v___jp_2494_:
{
lean_object* v___x_2495_; 
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
v___x_2495_ = lean_apply_5(v_inferType_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, lean_box(0));
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; uint8_t v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
v___x_2497_ = l_Lean_Expr_hasMVar(v_a_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2532_; 
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2495_, 0);
lean_dec(v_unused_2533_);
v___x_2499_ = v___x_2495_;
v_isShared_2500_ = v_isSharedCheck_2532_;
goto v_resetjp_2498_;
}
else
{
lean_dec(v___x_2495_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2532_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v_cache_2502_; lean_object* v_mctx_2503_; lean_object* v_zetaDeltaFVarIds_2504_; lean_object* v_postponed_2505_; lean_object* v_diag_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2531_; 
v___x_2501_ = lean_st_ref_take(v_a_2442_);
v_cache_2502_ = lean_ctor_get(v___x_2501_, 1);
v_mctx_2503_ = lean_ctor_get(v___x_2501_, 0);
v_zetaDeltaFVarIds_2504_ = lean_ctor_get(v___x_2501_, 2);
v_postponed_2505_ = lean_ctor_get(v___x_2501_, 3);
v_diag_2506_ = lean_ctor_get(v___x_2501_, 4);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2508_ = v___x_2501_;
v_isShared_2509_ = v_isSharedCheck_2531_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_diag_2506_);
lean_inc(v_postponed_2505_);
lean_inc(v_zetaDeltaFVarIds_2504_);
lean_inc(v_cache_2502_);
lean_inc(v_mctx_2503_);
lean_dec(v___x_2501_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2531_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v_inferType_2510_; lean_object* v_funInfo_2511_; lean_object* v_synthInstance_2512_; lean_object* v_whnf_2513_; lean_object* v_defEqTrans_2514_; lean_object* v_defEqPerm_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2530_; 
v_inferType_2510_ = lean_ctor_get(v_cache_2502_, 0);
v_funInfo_2511_ = lean_ctor_get(v_cache_2502_, 1);
v_synthInstance_2512_ = lean_ctor_get(v_cache_2502_, 2);
v_whnf_2513_ = lean_ctor_get(v_cache_2502_, 3);
v_defEqTrans_2514_ = lean_ctor_get(v_cache_2502_, 4);
v_defEqPerm_2515_ = lean_ctor_get(v_cache_2502_, 5);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_cache_2502_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2517_ = v_cache_2502_;
v_isShared_2518_ = v_isSharedCheck_2530_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_defEqPerm_2515_);
lean_inc(v_defEqTrans_2514_);
lean_inc(v_whnf_2513_);
lean_inc(v_synthInstance_2512_);
lean_inc(v_funInfo_2511_);
lean_inc(v_inferType_2510_);
lean_dec(v_cache_2502_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2530_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_inc(v_a_2496_);
v___x_2519_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2487_, v___x_2488_, v_inferType_2510_, v_a_2490_, v_a_2496_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2519_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_funInfo_2511_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_synthInstance_2512_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_whnf_2513_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_defEqTrans_2514_);
lean_ctor_set(v_reuseFailAlloc_2529_, 5, v_defEqPerm_2515_);
v___x_2521_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2521_);
v___x_2523_ = v___x_2508_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_mctx_2503_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_zetaDeltaFVarIds_2504_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_postponed_2505_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_diag_2506_);
v___x_2523_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2524_ = lean_st_ref_put(v_a_2442_, v___x_2523_);
if (v_isShared_2500_ == 0)
{
v___x_2526_ = v___x_2499_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2496_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2496_);
lean_dec(v_a_2490_);
return v___x_2495_;
}
}
else
{
lean_dec(v_a_2490_);
return v___x_2495_;
}
}
v_resetjp_2536_:
{
lean_object* v_inferType_2539_; lean_object* v___x_2540_; 
v_inferType_2539_ = lean_ctor_get(v_cache_2535_, 0);
lean_inc_ref(v_inferType_2539_);
lean_dec_ref(v_cache_2535_);
lean_inc(v_a_2490_);
v___x_2540_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2487_, v___x_2488_, v_inferType_2539_, v_a_2490_);
lean_dec_ref(v_inferType_2539_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; lean_object* v_toApplicative_2542_; lean_object* v_toFunctor_2543_; lean_object* v_toSeq_2544_; lean_object* v_toSeqLeft_2545_; lean_object* v_toSeqRight_2546_; lean_object* v___f_2547_; lean_object* v___f_2548_; lean_object* v___f_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; lean_object* v___f_2552_; lean_object* v___f_2553_; lean_object* v___f_2554_; lean_object* v___x_2556_; 
lean_del_object(v___x_2492_);
v___x_2541_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2542_ = lean_ctor_get(v___x_2541_, 0);
v_toFunctor_2543_ = lean_ctor_get(v_toApplicative_2542_, 0);
v_toSeq_2544_ = lean_ctor_get(v_toApplicative_2542_, 2);
v_toSeqLeft_2545_ = lean_ctor_get(v_toApplicative_2542_, 3);
v_toSeqRight_2546_ = lean_ctor_get(v_toApplicative_2542_, 4);
v___f_2547_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2548_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2543_, 2);
v___f_2549_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2549_, 0, v_toFunctor_2543_);
v___f_2550_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2550_, 0, v_toFunctor_2543_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___f_2549_);
lean_ctor_set(v___x_2551_, 1, v___f_2550_);
lean_inc(v_toSeqRight_2546_);
v___f_2552_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2552_, 0, v_toSeqRight_2546_);
lean_inc(v_toSeqLeft_2545_);
v___f_2553_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2553_, 0, v_toSeqLeft_2545_);
lean_inc(v_toSeq_2544_);
v___f_2554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2554_, 0, v_toSeq_2544_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 4, v___f_2552_);
lean_ctor_set(v___x_2537_, 3, v___f_2553_);
lean_ctor_set(v___x_2537_, 2, v___f_2554_);
lean_ctor_set(v___x_2537_, 1, v___f_2547_);
lean_ctor_set(v___x_2537_, 0, v___x_2551_);
v___x_2556_ = v___x_2537_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___f_2547_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v___f_2554_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v___f_2553_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v___f_2552_);
v___x_2556_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_toCold_2563_; lean_object* v_cancelTk_x3f_2564_; 
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___f_2548_);
v___x_2558_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2559_ = l_Lean_Core_instMonadRefCoreM;
v___x_2560_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2561_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2560_, v___x_2557_);
v___x_2562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2558_);
lean_ctor_set(v___x_2562_, 1, v___x_2559_);
lean_ctor_set(v___x_2562_, 2, v___x_2561_);
v_toCold_2563_ = lean_ctor_get(v_a_2443_, 0);
v_cancelTk_x3f_2564_ = lean_ctor_get(v_toCold_2563_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2564_) == 1)
{
lean_object* v_val_2565_; uint8_t v___x_2566_; 
v_val_2565_ = lean_ctor_get(v_cancelTk_x3f_2564_, 0);
v___x_2566_ = l_IO_CancelToken_isSet(v_val_2565_);
if (v___x_2566_ == 0)
{
lean_dec_ref_known(v___x_2562_, 3);
goto v___jp_2494_;
}
else
{
lean_object* v___x_2058__overap_2567_; lean_object* v___x_2568_; 
v___x_2058__overap_2567_ = l_Lean_throwInterruptException___redArg(v___x_2562_);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
v___x_2568_ = lean_apply_3(v___x_2058__overap_2567_, v_a_2443_, v_a_2444_, lean_box(0));
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_dec_ref_known(v___x_2568_, 1);
goto v___jp_2494_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_a_2490_);
lean_dec_ref(v_inferType_2440_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2562_, 3);
goto v___jp_2494_;
}
}
}
else
{
lean_object* v_val_2578_; lean_object* v___x_2580_; 
lean_del_object(v___x_2537_);
lean_dec(v_a_2490_);
lean_dec_ref(v_inferType_2440_);
v_val_2578_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_val_2578_);
lean_dec_ref_known(v___x_2540_, 1);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v_val_2578_);
v___x_2580_ = v___x_2492_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_val_2578_);
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
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_inferType_2440_);
v_a_2588_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2489_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2489_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_dec_ref(v_e_2439_);
goto v___jp_2446_;
}
}
v___jp_2446_:
{
lean_object* v___x_2447_; lean_object* v_toApplicative_2448_; lean_object* v_toFunctor_2449_; lean_object* v_toSeq_2450_; lean_object* v_toSeqLeft_2451_; lean_object* v_toSeqRight_2452_; lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; lean_object* v___f_2458_; lean_object* v___f_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v_toCold_2468_; lean_object* v_cancelTk_x3f_2469_; 
v___x_2447_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2448_ = lean_ctor_get(v___x_2447_, 0);
v_toFunctor_2449_ = lean_ctor_get(v_toApplicative_2448_, 0);
v_toSeq_2450_ = lean_ctor_get(v_toApplicative_2448_, 2);
v_toSeqLeft_2451_ = lean_ctor_get(v_toApplicative_2448_, 3);
v_toSeqRight_2452_ = lean_ctor_get(v_toApplicative_2448_, 4);
v___f_2453_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2454_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2449_, 2);
v___f_2455_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2455_, 0, v_toFunctor_2449_);
v___f_2456_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2456_, 0, v_toFunctor_2449_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___f_2455_);
lean_ctor_set(v___x_2457_, 1, v___f_2456_);
lean_inc(v_toSeqRight_2452_);
v___f_2458_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2458_, 0, v_toSeqRight_2452_);
lean_inc(v_toSeqLeft_2451_);
v___f_2459_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2459_, 0, v_toSeqLeft_2451_);
lean_inc(v_toSeq_2450_);
v___f_2460_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2460_, 0, v_toSeq_2450_);
v___x_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2457_);
lean_ctor_set(v___x_2461_, 1, v___f_2453_);
lean_ctor_set(v___x_2461_, 2, v___f_2460_);
lean_ctor_set(v___x_2461_, 3, v___f_2459_);
lean_ctor_set(v___x_2461_, 4, v___f_2458_);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___f_2454_);
v___x_2463_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2464_ = l_Lean_Core_instMonadRefCoreM;
v___x_2465_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2466_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2465_, v___x_2462_);
v___x_2467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2463_);
lean_ctor_set(v___x_2467_, 1, v___x_2464_);
lean_ctor_set(v___x_2467_, 2, v___x_2466_);
v_toCold_2468_ = lean_ctor_get(v_a_2443_, 0);
v_cancelTk_x3f_2469_ = lean_ctor_get(v_toCold_2468_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2469_) == 1)
{
lean_object* v_val_2470_; uint8_t v___x_2471_; 
v_val_2470_ = lean_ctor_get(v_cancelTk_x3f_2469_, 0);
v___x_2471_ = l_IO_CancelToken_isSet(v_val_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
lean_dec_ref_known(v___x_2467_, 3);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
v___x_2472_ = lean_apply_5(v_inferType_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, lean_box(0));
return v___x_2472_;
}
else
{
lean_object* v___x_2031__overap_2473_; lean_object* v___x_2474_; 
v___x_2031__overap_2473_ = l_Lean_throwInterruptException___redArg(v___x_2467_);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
v___x_2474_ = lean_apply_3(v___x_2031__overap_2473_, v_a_2443_, v_a_2444_, lean_box(0));
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v___x_2475_; 
lean_dec_ref_known(v___x_2474_, 1);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
v___x_2475_ = lean_apply_5(v_inferType_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, lean_box(0));
return v___x_2475_;
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_inferType_2440_);
v_a_2476_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2474_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2474_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
else
{
lean_object* v___x_2484_; 
lean_dec_ref_known(v___x_2467_, 3);
lean_inc(v_a_2444_);
lean_inc_ref(v_a_2443_);
lean_inc(v_a_2442_);
lean_inc_ref(v_a_2441_);
v___x_2484_ = lean_apply_5(v_inferType_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, lean_box(0));
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2596_, lean_object* v_inferType_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2596_, v_inferType_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2656_; uint8_t v_beta_2657_; 
v___x_2656_ = l_Lean_Meta_Context_config(v___y_2605_);
v_beta_2657_ = lean_ctor_get_uint8(v___x_2656_, 13);
if (v_beta_2657_ == 0)
{
lean_dec_ref(v___x_2656_);
goto v___jp_2610_;
}
else
{
uint8_t v_iota_2658_; 
v_iota_2658_ = lean_ctor_get_uint8(v___x_2656_, 12);
if (v_iota_2658_ == 0)
{
lean_dec_ref(v___x_2656_);
goto v___jp_2610_;
}
else
{
uint8_t v_zeta_2659_; 
v_zeta_2659_ = lean_ctor_get_uint8(v___x_2656_, 15);
if (v_zeta_2659_ == 0)
{
lean_dec_ref(v___x_2656_);
goto v___jp_2610_;
}
else
{
uint8_t v_zetaHave_2660_; 
v_zetaHave_2660_ = lean_ctor_get_uint8(v___x_2656_, 18);
if (v_zetaHave_2660_ == 0)
{
lean_dec_ref(v___x_2656_);
goto v___jp_2610_;
}
else
{
uint8_t v_zetaDelta_2661_; 
v_zetaDelta_2661_ = lean_ctor_get_uint8(v___x_2656_, 16);
if (v_zetaDelta_2661_ == 0)
{
lean_dec_ref(v___x_2656_);
goto v___jp_2610_;
}
else
{
uint8_t v_etaStruct_2662_; uint8_t v_proj_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v_etaStruct_2662_ = lean_ctor_get_uint8(v___x_2656_, 10);
v_proj_2663_ = lean_ctor_get_uint8(v___x_2656_, 14);
lean_dec_ref(v___x_2656_);
v___x_2664_ = lean_box(v_proj_2663_);
v___x_2665_ = lean_obj_tag_nat(v___x_2664_);
lean_dec(v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(2u);
v___x_2667_ = lean_nat_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
goto v___jp_2610_;
}
else
{
uint8_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = 0;
v___x_2669_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2662_, v___x_2668_);
if (v___x_2669_ == 0)
{
goto v___jp_2610_;
}
else
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_apply_5(v_x_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, lean_box(0));
return v___x_2670_;
}
}
}
}
}
}
}
v___jp_2610_:
{
lean_object* v___x_2611_; uint8_t v_foApprox_2612_; uint8_t v_ctxApprox_2613_; uint8_t v_quasiPatternApprox_2614_; uint8_t v_constApprox_2615_; uint8_t v_isDefEqStuckEx_2616_; uint8_t v_unificationHints_2617_; uint8_t v_proofIrrelevance_2618_; uint8_t v_assignSyntheticOpaque_2619_; uint8_t v_offsetCnstrs_2620_; uint8_t v_transparency_2621_; uint8_t v_univApprox_2622_; uint8_t v_zetaUnused_2623_; uint8_t v_canUnfoldPredicateConfig_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2655_; 
v___x_2611_ = l_Lean_Meta_Context_config(v___y_2605_);
v_foApprox_2612_ = lean_ctor_get_uint8(v___x_2611_, 0);
v_ctxApprox_2613_ = lean_ctor_get_uint8(v___x_2611_, 1);
v_quasiPatternApprox_2614_ = lean_ctor_get_uint8(v___x_2611_, 2);
v_constApprox_2615_ = lean_ctor_get_uint8(v___x_2611_, 3);
v_isDefEqStuckEx_2616_ = lean_ctor_get_uint8(v___x_2611_, 4);
v_unificationHints_2617_ = lean_ctor_get_uint8(v___x_2611_, 5);
v_proofIrrelevance_2618_ = lean_ctor_get_uint8(v___x_2611_, 6);
v_assignSyntheticOpaque_2619_ = lean_ctor_get_uint8(v___x_2611_, 7);
v_offsetCnstrs_2620_ = lean_ctor_get_uint8(v___x_2611_, 8);
v_transparency_2621_ = lean_ctor_get_uint8(v___x_2611_, 9);
v_univApprox_2622_ = lean_ctor_get_uint8(v___x_2611_, 11);
v_zetaUnused_2623_ = lean_ctor_get_uint8(v___x_2611_, 17);
v_canUnfoldPredicateConfig_2624_ = lean_ctor_get_uint8(v___x_2611_, 19);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2626_ = v___x_2611_;
v_isShared_2627_ = v_isSharedCheck_2655_;
goto v_resetjp_2625_;
}
else
{
lean_dec(v___x_2611_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2655_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
uint8_t v___x_2628_; uint8_t v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2632_; 
v___x_2628_ = 1;
v___x_2629_ = 0;
v___x_2630_ = 2;
if (v_isShared_2627_ == 0)
{
v___x_2632_ = v___x_2626_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 0, v_foApprox_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 1, v_ctxApprox_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 2, v_quasiPatternApprox_2614_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 3, v_constApprox_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 4, v_isDefEqStuckEx_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 5, v_unificationHints_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 6, v_proofIrrelevance_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 7, v_assignSyntheticOpaque_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 8, v_offsetCnstrs_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 9, v_transparency_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 11, v_univApprox_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 17, v_zetaUnused_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2654_, 19, v_canUnfoldPredicateConfig_2624_);
v___x_2632_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
uint8_t v_trackZetaDelta_2633_; lean_object* v_zetaDeltaSet_2634_; lean_object* v_lctx_2635_; lean_object* v_localInstances_2636_; lean_object* v_defEqCtx_x3f_2637_; lean_object* v_synthPendingDepth_2638_; lean_object* v_customCanUnfoldPredicate_x3f_2639_; uint8_t v_univApprox_2640_; uint8_t v_inTypeClassResolution_2641_; uint8_t v_cacheInferType_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2652_; 
lean_ctor_set_uint8(v___x_2632_, 10, v___x_2629_);
lean_ctor_set_uint8(v___x_2632_, 12, v___x_2628_);
lean_ctor_set_uint8(v___x_2632_, 13, v___x_2628_);
lean_ctor_set_uint8(v___x_2632_, 14, v___x_2630_);
lean_ctor_set_uint8(v___x_2632_, 15, v___x_2628_);
lean_ctor_set_uint8(v___x_2632_, 16, v___x_2628_);
lean_ctor_set_uint8(v___x_2632_, 18, v___x_2628_);
v_trackZetaDelta_2633_ = lean_ctor_get_uint8(v___y_2605_, sizeof(void*)*7);
v_zetaDeltaSet_2634_ = lean_ctor_get(v___y_2605_, 1);
v_lctx_2635_ = lean_ctor_get(v___y_2605_, 2);
v_localInstances_2636_ = lean_ctor_get(v___y_2605_, 3);
v_defEqCtx_x3f_2637_ = lean_ctor_get(v___y_2605_, 4);
v_synthPendingDepth_2638_ = lean_ctor_get(v___y_2605_, 5);
v_customCanUnfoldPredicate_x3f_2639_ = lean_ctor_get(v___y_2605_, 6);
v_univApprox_2640_ = lean_ctor_get_uint8(v___y_2605_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2641_ = lean_ctor_get_uint8(v___y_2605_, sizeof(void*)*7 + 2);
v_cacheInferType_2642_ = lean_ctor_get_uint8(v___y_2605_, sizeof(void*)*7 + 3);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___y_2605_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v___y_2605_, 0);
lean_dec(v_unused_2653_);
v___x_2644_ = v___y_2605_;
v_isShared_2645_ = v_isSharedCheck_2652_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2639_);
lean_inc(v_synthPendingDepth_2638_);
lean_inc(v_defEqCtx_x3f_2637_);
lean_inc(v_localInstances_2636_);
lean_inc(v_lctx_2635_);
lean_inc(v_zetaDeltaSet_2634_);
lean_dec(v___y_2605_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2652_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint64_t v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2646_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2632_);
v___x_2647_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2647_, 0, v___x_2632_);
lean_ctor_set_uint64(v___x_2647_, sizeof(void*)*1, v___x_2646_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2647_);
v___x_2649_ = v___x_2644_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_zetaDeltaSet_2634_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_lctx_2635_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_localInstances_2636_);
lean_ctor_set(v_reuseFailAlloc_2651_, 4, v_defEqCtx_x3f_2637_);
lean_ctor_set(v_reuseFailAlloc_2651_, 5, v_synthPendingDepth_2638_);
lean_ctor_set(v_reuseFailAlloc_2651_, 6, v_customCanUnfoldPredicate_x3f_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*7, v_trackZetaDelta_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*7 + 1, v_univApprox_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*7 + 3, v_cacheInferType_2642_);
v___x_2649_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_apply_5(v_x_2604_, v___x_2649_, v___y_2606_, v___y_2607_, v___y_2608_, lean_box(0));
return v___x_2650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___y_2685_; lean_object* v___x_2702_; uint8_t v_transparency_2703_; uint8_t v___x_2704_; uint8_t v___x_2705_; 
v___x_2702_ = l_Lean_Meta_Context_config(v_a_2679_);
v_transparency_2703_ = lean_ctor_get_uint8(v___x_2702_, 9);
lean_dec_ref(v___x_2702_);
v___x_2704_ = 1;
v___x_2705_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; 
lean_inc(v_a_2682_);
lean_inc_ref(v_a_2681_);
lean_inc(v_a_2680_);
lean_inc_ref(v_a_2679_);
v___x_2706_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
v___y_2685_ = v___x_2706_;
goto v___jp_2684_;
}
else
{
lean_object* v_keyedConfig_2707_; uint8_t v_trackZetaDelta_2708_; lean_object* v_zetaDeltaSet_2709_; lean_object* v_lctx_2710_; lean_object* v_localInstances_2711_; lean_object* v_defEqCtx_x3f_2712_; lean_object* v_synthPendingDepth_2713_; lean_object* v_customCanUnfoldPredicate_x3f_2714_; uint8_t v_univApprox_2715_; uint8_t v_inTypeClassResolution_2716_; uint8_t v_cacheInferType_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_keyedConfig_2707_ = lean_ctor_get(v_a_2679_, 0);
v_trackZetaDelta_2708_ = lean_ctor_get_uint8(v_a_2679_, sizeof(void*)*7);
v_zetaDeltaSet_2709_ = lean_ctor_get(v_a_2679_, 1);
v_lctx_2710_ = lean_ctor_get(v_a_2679_, 2);
v_localInstances_2711_ = lean_ctor_get(v_a_2679_, 3);
v_defEqCtx_x3f_2712_ = lean_ctor_get(v_a_2679_, 4);
v_synthPendingDepth_2713_ = lean_ctor_get(v_a_2679_, 5);
v_customCanUnfoldPredicate_x3f_2714_ = lean_ctor_get(v_a_2679_, 6);
v_univApprox_2715_ = lean_ctor_get_uint8(v_a_2679_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2716_ = lean_ctor_get_uint8(v_a_2679_, sizeof(void*)*7 + 2);
v_cacheInferType_2717_ = lean_ctor_get_uint8(v_a_2679_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2707_);
v___x_2718_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2704_, v_keyedConfig_2707_);
lean_inc(v_customCanUnfoldPredicate_x3f_2714_);
lean_inc(v_synthPendingDepth_2713_);
lean_inc(v_defEqCtx_x3f_2712_);
lean_inc_ref(v_localInstances_2711_);
lean_inc_ref(v_lctx_2710_);
lean_inc(v_zetaDeltaSet_2709_);
v___x_2719_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_zetaDeltaSet_2709_);
lean_ctor_set(v___x_2719_, 2, v_lctx_2710_);
lean_ctor_set(v___x_2719_, 3, v_localInstances_2711_);
lean_ctor_set(v___x_2719_, 4, v_defEqCtx_x3f_2712_);
lean_ctor_set(v___x_2719_, 5, v_synthPendingDepth_2713_);
lean_ctor_set(v___x_2719_, 6, v_customCanUnfoldPredicate_x3f_2714_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7, v_trackZetaDelta_2708_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 1, v_univApprox_2715_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2716_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 3, v_cacheInferType_2717_);
lean_inc(v_a_2682_);
lean_inc_ref(v_a_2681_);
lean_inc(v_a_2680_);
v___x_2720_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2678_, v___x_2719_, v_a_2680_, v_a_2681_, v_a_2682_);
v___y_2685_ = v___x_2720_;
goto v___jp_2684_;
}
v___jp_2684_:
{
if (lean_obj_tag(v___y_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_a_2686_ = lean_ctor_get(v___y_2685_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___y_2685_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___y_2685_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___y_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_a_2694_ = lean_ctor_get(v___y_2685_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___y_2685_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___y_2685_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___y_2685_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2728_, lean_object* v_x_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___y_2736_; lean_object* v___x_2753_; uint8_t v_transparency_2754_; uint8_t v___x_2755_; uint8_t v___x_2756_; 
v___x_2753_ = l_Lean_Meta_Context_config(v_a_2730_);
v_transparency_2754_ = lean_ctor_get_uint8(v___x_2753_, 9);
lean_dec_ref(v___x_2753_);
v___x_2755_ = 1;
v___x_2756_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; 
lean_inc(v_a_2733_);
lean_inc_ref(v_a_2732_);
lean_inc(v_a_2731_);
lean_inc_ref(v_a_2730_);
v___x_2757_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
v___y_2736_ = v___x_2757_;
goto v___jp_2735_;
}
else
{
lean_object* v_keyedConfig_2758_; uint8_t v_trackZetaDelta_2759_; lean_object* v_zetaDeltaSet_2760_; lean_object* v_lctx_2761_; lean_object* v_localInstances_2762_; lean_object* v_defEqCtx_x3f_2763_; lean_object* v_synthPendingDepth_2764_; lean_object* v_customCanUnfoldPredicate_x3f_2765_; uint8_t v_univApprox_2766_; uint8_t v_inTypeClassResolution_2767_; uint8_t v_cacheInferType_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_keyedConfig_2758_ = lean_ctor_get(v_a_2730_, 0);
v_trackZetaDelta_2759_ = lean_ctor_get_uint8(v_a_2730_, sizeof(void*)*7);
v_zetaDeltaSet_2760_ = lean_ctor_get(v_a_2730_, 1);
v_lctx_2761_ = lean_ctor_get(v_a_2730_, 2);
v_localInstances_2762_ = lean_ctor_get(v_a_2730_, 3);
v_defEqCtx_x3f_2763_ = lean_ctor_get(v_a_2730_, 4);
v_synthPendingDepth_2764_ = lean_ctor_get(v_a_2730_, 5);
v_customCanUnfoldPredicate_x3f_2765_ = lean_ctor_get(v_a_2730_, 6);
v_univApprox_2766_ = lean_ctor_get_uint8(v_a_2730_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2767_ = lean_ctor_get_uint8(v_a_2730_, sizeof(void*)*7 + 2);
v_cacheInferType_2768_ = lean_ctor_get_uint8(v_a_2730_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2758_);
v___x_2769_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2755_, v_keyedConfig_2758_);
lean_inc(v_customCanUnfoldPredicate_x3f_2765_);
lean_inc(v_synthPendingDepth_2764_);
lean_inc(v_defEqCtx_x3f_2763_);
lean_inc_ref(v_localInstances_2762_);
lean_inc_ref(v_lctx_2761_);
lean_inc(v_zetaDeltaSet_2760_);
v___x_2770_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v_zetaDeltaSet_2760_);
lean_ctor_set(v___x_2770_, 2, v_lctx_2761_);
lean_ctor_set(v___x_2770_, 3, v_localInstances_2762_);
lean_ctor_set(v___x_2770_, 4, v_defEqCtx_x3f_2763_);
lean_ctor_set(v___x_2770_, 5, v_synthPendingDepth_2764_);
lean_ctor_set(v___x_2770_, 6, v_customCanUnfoldPredicate_x3f_2765_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*7, v_trackZetaDelta_2759_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*7 + 1, v_univApprox_2766_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2767_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*7 + 3, v_cacheInferType_2768_);
lean_inc(v_a_2733_);
lean_inc_ref(v_a_2732_);
lean_inc(v_a_2731_);
v___x_2771_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2729_, v___x_2770_, v_a_2731_, v_a_2732_, v_a_2733_);
v___y_2736_ = v___x_2771_;
goto v___jp_2735_;
}
v___jp_2735_:
{
if (lean_obj_tag(v___y_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
v_a_2737_ = lean_ctor_get(v___y_2736_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___y_2736_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___y_2736_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___y_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_a_2745_ = lean_ctor_get(v___y_2736_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___y_2736_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___y_2736_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___y_2736_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2772_, lean_object* v_x_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2772_, v_x_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
return v_res_2779_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = l_Lean_interruptExceptionId;
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v___x_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_){
_start:
{
lean_object* v_ks_2802_; lean_object* v_vs_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2829_; 
v_ks_2802_ = lean_ctor_get(v_x_2798_, 0);
v_vs_2803_ = lean_ctor_get(v_x_2798_, 1);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_x_2798_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2805_ = v_x_2798_;
v_isShared_2806_ = v_isSharedCheck_2829_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_vs_2803_);
lean_inc(v_ks_2802_);
lean_dec(v_x_2798_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2829_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2814_ = lean_array_get_size(v_ks_2802_);
v___x_2815_ = lean_nat_dec_lt(v_x_2799_, v___x_2814_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_del_object(v___x_2805_);
lean_dec(v_x_2799_);
v___x_2816_ = lean_array_push(v_ks_2802_, v_x_2800_);
v___x_2817_ = lean_array_push(v_vs_2803_, v_x_2801_);
v___x_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
return v___x_2818_;
}
else
{
lean_object* v_expr_2819_; uint64_t v_configKey_2820_; lean_object* v_k_x27_2821_; lean_object* v_expr_2822_; uint64_t v_configKey_2823_; uint8_t v___x_2824_; 
v_expr_2819_ = lean_ctor_get(v_x_2800_, 0);
v_configKey_2820_ = lean_ctor_get_uint64(v_x_2800_, sizeof(void*)*1);
v_k_x27_2821_ = lean_array_fget_borrowed(v_ks_2802_, v_x_2799_);
v_expr_2822_ = lean_ctor_get(v_k_x27_2821_, 0);
v_configKey_2823_ = lean_ctor_get_uint64(v_k_x27_2821_, sizeof(void*)*1);
v___x_2824_ = lean_expr_equal(v_expr_2819_, v_expr_2822_);
if (v___x_2824_ == 0)
{
goto v___jp_2807_;
}
else
{
uint8_t v___x_2825_; 
v___x_2825_ = lean_uint64_dec_eq(v_configKey_2820_, v_configKey_2823_);
if (v___x_2825_ == 0)
{
goto v___jp_2807_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_del_object(v___x_2805_);
v___x_2826_ = lean_array_fset(v_ks_2802_, v_x_2799_, v_x_2800_);
v___x_2827_ = lean_array_fset(v_vs_2803_, v_x_2799_, v_x_2801_);
lean_dec(v_x_2799_);
v___x_2828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
return v___x_2828_;
}
}
}
v___jp_2807_:
{
lean_object* v___x_2809_; 
if (v_isShared_2806_ == 0)
{
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_ks_2802_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_vs_2803_);
v___x_2809_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_unsigned_to_nat(1u);
v___x_2811_ = lean_nat_add(v_x_2799_, v___x_2810_);
lean_dec(v_x_2799_);
v_x_2798_ = v___x_2809_;
v_x_2799_ = v___x_2811_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2830_, lean_object* v_k_2831_, lean_object* v_v_2832_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2830_, v___x_2833_, v_k_2831_, v_v_2832_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2835_, size_t v_x_2836_, size_t v_x_2837_, lean_object* v_x_2838_, lean_object* v_x_2839_){
_start:
{
if (lean_obj_tag(v_x_2835_) == 0)
{
lean_object* v_es_2840_; size_t v___x_2841_; size_t v___x_2842_; lean_object* v_j_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_es_2840_ = lean_ctor_get(v_x_2835_, 0);
v___x_2841_ = ((size_t)31ULL);
v___x_2842_ = lean_usize_land(v_x_2836_, v___x_2841_);
v_j_2843_ = lean_usize_to_nat(v___x_2842_);
v___x_2844_ = lean_array_get_size(v_es_2840_);
v___x_2845_ = lean_nat_dec_lt(v_j_2843_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_dec(v_j_2843_);
lean_dec(v_x_2839_);
lean_dec_ref(v_x_2838_);
return v_x_2835_;
}
else
{
lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2890_; 
lean_inc_ref(v_es_2840_);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_x_2835_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; 
v_unused_2891_ = lean_ctor_get(v_x_2835_, 0);
lean_dec(v_unused_2891_);
v___x_2847_ = v_x_2835_;
v_isShared_2848_ = v_isSharedCheck_2890_;
goto v_resetjp_2846_;
}
else
{
lean_dec(v_x_2835_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2890_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v_v_2849_; lean_object* v___x_2850_; lean_object* v_xs_x27_2851_; lean_object* v___y_2853_; 
v_v_2849_ = lean_array_fget(v_es_2840_, v_j_2843_);
v___x_2850_ = lean_box(0);
v_xs_x27_2851_ = lean_array_fset(v_es_2840_, v_j_2843_, v___x_2850_);
switch(lean_obj_tag(v_v_2849_))
{
case 0:
{
lean_object* v_key_2858_; lean_object* v_val_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2875_; 
v_key_2858_ = lean_ctor_get(v_v_2849_, 0);
v_val_2859_ = lean_ctor_get(v_v_2849_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_v_2849_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2861_ = v_v_2849_;
v_isShared_2862_ = v_isSharedCheck_2875_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_val_2859_);
lean_inc(v_key_2858_);
lean_dec(v_v_2849_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2875_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_expr_2866_; uint64_t v_configKey_2867_; lean_object* v_expr_2868_; uint64_t v_configKey_2869_; uint8_t v___x_2870_; 
v_expr_2866_ = lean_ctor_get(v_x_2838_, 0);
v_configKey_2867_ = lean_ctor_get_uint64(v_x_2838_, sizeof(void*)*1);
v_expr_2868_ = lean_ctor_get(v_key_2858_, 0);
v_configKey_2869_ = lean_ctor_get_uint64(v_key_2858_, sizeof(void*)*1);
v___x_2870_ = lean_expr_equal(v_expr_2866_, v_expr_2868_);
if (v___x_2870_ == 0)
{
lean_del_object(v___x_2861_);
goto v___jp_2863_;
}
else
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_uint64_dec_eq(v_configKey_2867_, v_configKey_2869_);
if (v___x_2871_ == 0)
{
lean_del_object(v___x_2861_);
goto v___jp_2863_;
}
else
{
lean_object* v___x_2873_; 
lean_dec(v_val_2859_);
lean_dec(v_key_2858_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v_x_2839_);
lean_ctor_set(v___x_2861_, 0, v_x_2838_);
v___x_2873_ = v___x_2861_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_x_2838_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_x_2839_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
v___y_2853_ = v___x_2873_;
goto v___jp_2852_;
}
}
}
v___jp_2863_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2858_, v_val_2859_, v_x_2838_, v_x_2839_);
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
v___y_2853_ = v___x_2865_;
goto v___jp_2852_;
}
}
}
case 1:
{
lean_object* v_node_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2888_; 
v_node_2876_ = lean_ctor_get(v_v_2849_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_v_2849_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2878_ = v_v_2849_;
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_node_2876_);
lean_dec(v_v_2849_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
size_t v___x_2880_; size_t v___x_2881_; size_t v___x_2882_; size_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2880_ = ((size_t)5ULL);
v___x_2881_ = lean_usize_shift_right(v_x_2836_, v___x_2880_);
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_add(v_x_2837_, v___x_2882_);
v___x_2884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2876_, v___x_2881_, v___x_2883_, v_x_2838_, v_x_2839_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2884_);
v___x_2886_ = v___x_2878_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
v___y_2853_ = v___x_2886_;
goto v___jp_2852_;
}
}
}
default: 
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_x_2838_);
lean_ctor_set(v___x_2889_, 1, v_x_2839_);
v___y_2853_ = v___x_2889_;
goto v___jp_2852_;
}
}
v___jp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = lean_array_fset(v_xs_x27_2851_, v_j_2843_, v___y_2853_);
lean_dec(v_j_2843_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2854_);
v___x_2856_ = v___x_2847_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
else
{
lean_object* v_ks_2892_; lean_object* v_vs_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2911_; 
v_ks_2892_ = lean_ctor_get(v_x_2835_, 0);
v_vs_2893_ = lean_ctor_get(v_x_2835_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_x_2835_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2895_ = v_x_2835_;
v_isShared_2896_ = v_isSharedCheck_2911_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_vs_2893_);
lean_inc(v_ks_2892_);
lean_dec(v_x_2835_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2911_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_ks_2892_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_vs_2893_);
v___x_2898_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v_newNode_2899_; size_t v___x_2900_; uint8_t v___x_2901_; 
v_newNode_2899_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2898_, v_x_2838_, v_x_2839_);
v___x_2900_ = ((size_t)7ULL);
v___x_2901_ = lean_usize_dec_le(v___x_2900_, v_x_2837_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2902_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2899_);
v___x_2903_ = lean_unsigned_to_nat(4u);
v___x_2904_ = lean_nat_dec_lt(v___x_2902_, v___x_2903_);
lean_dec(v___x_2902_);
if (v___x_2904_ == 0)
{
lean_object* v_ks_2905_; lean_object* v_vs_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_ks_2905_ = lean_ctor_get(v_newNode_2899_, 0);
lean_inc_ref(v_ks_2905_);
v_vs_2906_ = lean_ctor_get(v_newNode_2899_, 1);
lean_inc_ref(v_vs_2906_);
lean_dec_ref(v_newNode_2899_);
v___x_2907_ = lean_unsigned_to_nat(0u);
v___x_2908_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2909_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2837_, v_ks_2905_, v_vs_2906_, v___x_2907_, v___x_2908_);
lean_dec_ref(v_vs_2906_);
lean_dec_ref(v_ks_2905_);
return v___x_2909_;
}
else
{
return v_newNode_2899_;
}
}
else
{
return v_newNode_2899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2912_, lean_object* v_keys_2913_, lean_object* v_vals_2914_, lean_object* v_i_2915_, lean_object* v_entries_2916_){
_start:
{
lean_object* v___x_2917_; uint8_t v___x_2918_; 
v___x_2917_ = lean_array_get_size(v_keys_2913_);
v___x_2918_ = lean_nat_dec_lt(v_i_2915_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_dec(v_i_2915_);
return v_entries_2916_;
}
else
{
lean_object* v_k_2919_; lean_object* v_expr_2920_; uint64_t v_configKey_2921_; lean_object* v_v_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; size_t v_h_2925_; size_t v___x_2926_; lean_object* v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v_h_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_k_2919_ = lean_array_fget_borrowed(v_keys_2913_, v_i_2915_);
v_expr_2920_ = lean_ctor_get(v_k_2919_, 0);
v_configKey_2921_ = lean_ctor_get_uint64(v_k_2919_, sizeof(void*)*1);
v_v_2922_ = lean_array_fget_borrowed(v_vals_2914_, v_i_2915_);
v___x_2923_ = l_Lean_Expr_hash(v_expr_2920_);
v___x_2924_ = lean_uint64_mix_hash(v___x_2923_, v_configKey_2921_);
v_h_2925_ = lean_uint64_to_usize(v___x_2924_);
v___x_2926_ = ((size_t)5ULL);
v___x_2927_ = lean_unsigned_to_nat(1u);
v___x_2928_ = ((size_t)1ULL);
v___x_2929_ = lean_usize_sub(v_depth_2912_, v___x_2928_);
v___x_2930_ = lean_usize_mul(v___x_2926_, v___x_2929_);
v_h_2931_ = lean_usize_shift_right(v_h_2925_, v___x_2930_);
v___x_2932_ = lean_nat_add(v_i_2915_, v___x_2927_);
lean_dec(v_i_2915_);
lean_inc(v_v_2922_);
lean_inc(v_k_2919_);
v___x_2933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2916_, v_h_2931_, v_depth_2912_, v_k_2919_, v_v_2922_);
v_i_2915_ = v___x_2932_;
v_entries_2916_ = v___x_2933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2935_, lean_object* v_keys_2936_, lean_object* v_vals_2937_, lean_object* v_i_2938_, lean_object* v_entries_2939_){
_start:
{
size_t v_depth_boxed_2940_; lean_object* v_res_2941_; 
v_depth_boxed_2940_ = lean_unbox_usize(v_depth_2935_);
lean_dec(v_depth_2935_);
v_res_2941_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2940_, v_keys_2936_, v_vals_2937_, v_i_2938_, v_entries_2939_);
lean_dec_ref(v_vals_2937_);
lean_dec_ref(v_keys_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2942_, lean_object* v_x_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_){
_start:
{
size_t v_x_2418__boxed_2947_; size_t v_x_2419__boxed_2948_; lean_object* v_res_2949_; 
v_x_2418__boxed_2947_ = lean_unbox_usize(v_x_2943_);
lean_dec(v_x_2943_);
v_x_2419__boxed_2948_ = lean_unbox_usize(v_x_2944_);
lean_dec(v_x_2944_);
v_res_2949_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2942_, v_x_2418__boxed_2947_, v_x_2419__boxed_2948_, v_x_2945_, v_x_2946_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2950_, lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
lean_object* v_expr_2953_; uint64_t v_configKey_2954_; uint64_t v___x_2955_; uint64_t v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; lean_object* v___x_2959_; 
v_expr_2953_ = lean_ctor_get(v_x_2951_, 0);
v_configKey_2954_ = lean_ctor_get_uint64(v_x_2951_, sizeof(void*)*1);
v___x_2955_ = l_Lean_Expr_hash(v_expr_2953_);
v___x_2956_ = lean_uint64_mix_hash(v___x_2955_, v_configKey_2954_);
v___x_2957_ = lean_uint64_to_usize(v___x_2956_);
v___x_2958_ = ((size_t)1ULL);
v___x_2959_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2950_, v___x_2957_, v___x_2958_, v_x_2951_, v_x_2952_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2960_, lean_object* v_vals_2961_, lean_object* v_i_2962_, lean_object* v_k_2963_){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_array_get_size(v_keys_2960_);
v___x_2969_ = lean_nat_dec_lt(v_i_2962_, v___x_2968_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; 
lean_dec(v_i_2962_);
v___x_2970_ = lean_box(0);
return v___x_2970_;
}
else
{
lean_object* v_expr_2971_; uint64_t v_configKey_2972_; lean_object* v_k_x27_2973_; lean_object* v_expr_2974_; uint64_t v_configKey_2975_; uint8_t v___x_2976_; 
v_expr_2971_ = lean_ctor_get(v_k_2963_, 0);
v_configKey_2972_ = lean_ctor_get_uint64(v_k_2963_, sizeof(void*)*1);
v_k_x27_2973_ = lean_array_fget_borrowed(v_keys_2960_, v_i_2962_);
v_expr_2974_ = lean_ctor_get(v_k_x27_2973_, 0);
v_configKey_2975_ = lean_ctor_get_uint64(v_k_x27_2973_, sizeof(void*)*1);
v___x_2976_ = lean_expr_equal(v_expr_2971_, v_expr_2974_);
if (v___x_2976_ == 0)
{
goto v___jp_2964_;
}
else
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_uint64_dec_eq(v_configKey_2972_, v_configKey_2975_);
if (v___x_2977_ == 0)
{
goto v___jp_2964_;
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_array_fget_borrowed(v_vals_2961_, v_i_2962_);
lean_dec(v_i_2962_);
lean_inc(v___x_2978_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
}
}
v___jp_2964_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_unsigned_to_nat(1u);
v___x_2966_ = lean_nat_add(v_i_2962_, v___x_2965_);
lean_dec(v_i_2962_);
v_i_2962_ = v___x_2966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_2980_, lean_object* v_vals_2981_, lean_object* v_i_2982_, lean_object* v_k_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_2980_, v_vals_2981_, v_i_2982_, v_k_2983_);
lean_dec_ref(v_k_2983_);
lean_dec_ref(v_vals_2981_);
lean_dec_ref(v_keys_2980_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_2985_, size_t v_x_2986_, lean_object* v_x_2987_){
_start:
{
if (lean_obj_tag(v_x_2985_) == 0)
{
lean_object* v_es_2988_; lean_object* v___x_2989_; size_t v___x_2990_; size_t v___x_2991_; lean_object* v_j_2992_; lean_object* v___x_2993_; 
v_es_2988_ = lean_ctor_get(v_x_2985_, 0);
v___x_2989_ = lean_box(2);
v___x_2990_ = ((size_t)31ULL);
v___x_2991_ = lean_usize_land(v_x_2986_, v___x_2990_);
v_j_2992_ = lean_usize_to_nat(v___x_2991_);
v___x_2993_ = lean_array_get_borrowed(v___x_2989_, v_es_2988_, v_j_2992_);
lean_dec(v_j_2992_);
switch(lean_obj_tag(v___x_2993_))
{
case 0:
{
lean_object* v_key_2994_; lean_object* v_val_2995_; lean_object* v_expr_2996_; uint64_t v_configKey_2997_; lean_object* v_expr_2998_; uint64_t v_configKey_2999_; uint8_t v___x_3000_; 
v_key_2994_ = lean_ctor_get(v___x_2993_, 0);
v_val_2995_ = lean_ctor_get(v___x_2993_, 1);
v_expr_2996_ = lean_ctor_get(v_x_2987_, 0);
v_configKey_2997_ = lean_ctor_get_uint64(v_x_2987_, sizeof(void*)*1);
v_expr_2998_ = lean_ctor_get(v_key_2994_, 0);
v_configKey_2999_ = lean_ctor_get_uint64(v_key_2994_, sizeof(void*)*1);
v___x_3000_ = lean_expr_equal(v_expr_2996_, v_expr_2998_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_box(0);
return v___x_3001_;
}
else
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_uint64_dec_eq(v_configKey_2997_, v_configKey_2999_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_box(0);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; 
lean_inc(v_val_2995_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v_val_2995_);
return v___x_3004_;
}
}
}
case 1:
{
lean_object* v_node_3005_; size_t v___x_3006_; size_t v___x_3007_; 
v_node_3005_ = lean_ctor_get(v___x_2993_, 0);
v___x_3006_ = ((size_t)5ULL);
v___x_3007_ = lean_usize_shift_right(v_x_2986_, v___x_3006_);
v_x_2985_ = v_node_3005_;
v_x_2986_ = v___x_3007_;
goto _start;
}
default: 
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_box(0);
return v___x_3009_;
}
}
}
else
{
lean_object* v_ks_3010_; lean_object* v_vs_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_ks_3010_ = lean_ctor_get(v_x_2985_, 0);
v_vs_3011_ = lean_ctor_get(v_x_2985_, 1);
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3010_, v_vs_3011_, v___x_3012_, v_x_2987_);
return v___x_3013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3014_, lean_object* v_x_3015_, lean_object* v_x_3016_){
_start:
{
size_t v_x_2618__boxed_3017_; lean_object* v_res_3018_; 
v_x_2618__boxed_3017_ = lean_unbox_usize(v_x_3015_);
lean_dec(v_x_3015_);
v_res_3018_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3014_, v_x_2618__boxed_3017_, v_x_3016_);
lean_dec_ref(v_x_3016_);
lean_dec_ref(v_x_3014_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
lean_object* v_expr_3021_; uint64_t v_configKey_3022_; uint64_t v___x_3023_; uint64_t v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; 
v_expr_3021_ = lean_ctor_get(v_x_3020_, 0);
v_configKey_3022_ = lean_ctor_get_uint64(v_x_3020_, sizeof(void*)*1);
v___x_3023_ = l_Lean_Expr_hash(v_expr_3021_);
v___x_3024_ = lean_uint64_mix_hash(v___x_3023_, v_configKey_3022_);
v___x_3025_ = lean_uint64_to_usize(v___x_3024_);
v___x_3026_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3019_, v___x_3025_, v_x_3020_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3027_, v_x_3028_);
lean_dec_ref(v_x_3028_);
lean_dec_ref(v_x_3027_);
return v_res_3029_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
switch(lean_obj_tag(v_e_3033_))
{
case 0:
{
lean_object* v_deBruijnIndex_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v_deBruijnIndex_3071_ = lean_ctor_get(v_e_3033_, 0);
lean_inc(v_deBruijnIndex_3071_);
lean_dec_ref_known(v_e_3033_, 1);
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3073_ = l_Lean_mkBVar(v_deBruijnIndex_3071_);
v___x_3074_ = l_Lean_MessageData_ofExpr(v___x_3073_);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3072_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3075_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3076_;
}
case 1:
{
lean_object* v_fvarId_3077_; lean_object* v___x_3078_; 
v_fvarId_3077_ = lean_ctor_get(v_e_3033_, 0);
lean_inc(v_fvarId_3077_);
lean_dec_ref_known(v_e_3033_, 1);
v___x_3078_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3077_, v_a_3034_, v_a_3036_, v_a_3037_);
return v___x_3078_;
}
case 2:
{
lean_object* v_mvarId_3079_; lean_object* v___x_3080_; 
v_mvarId_3079_ = lean_ctor_get(v_e_3033_, 0);
lean_inc(v_mvarId_3079_);
lean_dec_ref_known(v_e_3033_, 1);
v___x_3080_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3079_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3080_;
}
case 3:
{
lean_object* v_u_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_u_3081_ = lean_ctor_get(v_e_3033_, 0);
lean_inc(v_u_3081_);
lean_dec_ref_known(v_e_3033_, 1);
v___x_3082_ = l_Lean_Level_succ___override(v_u_3081_);
v___x_3083_ = l_Lean_mkSort(v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
case 4:
{
lean_object* v_declName_3085_; lean_object* v_us_3086_; 
v_declName_3085_ = lean_ctor_get(v_e_3033_, 0);
lean_inc(v_declName_3085_);
v_us_3086_ = lean_ctor_get(v_e_3033_, 1);
lean_inc(v_us_3086_);
if (lean_obj_tag(v_us_3086_) == 0)
{
lean_object* v___x_3103_; 
lean_dec_ref_known(v_e_3033_, 2);
v___x_3103_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3085_, v_us_3086_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3103_;
}
else
{
uint8_t v_cacheInferType_3104_; 
v_cacheInferType_3104_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3104_ == 0)
{
lean_dec_ref_known(v_e_3033_, 2);
goto v___jp_3087_;
}
else
{
uint8_t v___x_3105_; 
v___x_3105_ = l_Lean_Expr_hasMVar(v_e_3033_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3172_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3172_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3172_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3151_; lean_object* v_cache_3152_; lean_object* v_inferType_3153_; lean_object* v___x_3154_; 
v___x_3151_ = lean_st_ref_get(v_a_3035_);
v_cache_3152_ = lean_ctor_get(v___x_3151_, 1);
lean_inc_ref(v_cache_3152_);
lean_dec(v___x_3151_);
v_inferType_3153_ = lean_ctor_get(v_cache_3152_, 0);
lean_inc_ref(v_inferType_3153_);
lean_dec_ref(v_cache_3152_);
v___x_3154_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3153_, v_a_3107_);
lean_dec_ref(v_inferType_3153_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_toCold_3155_; lean_object* v_cancelTk_x3f_3156_; 
lean_del_object(v___x_3109_);
v_toCold_3155_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3156_ = lean_ctor_get(v_toCold_3155_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3156_) == 1)
{
lean_object* v_val_3157_; uint8_t v___x_3158_; 
v_val_3157_ = lean_ctor_get(v_cancelTk_x3f_3156_, 0);
v___x_3158_ = l_IO_CancelToken_isSet(v_val_3157_);
if (v___x_3158_ == 0)
{
goto v___jp_3111_;
}
else
{
lean_object* v___x_3159_; lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3107_);
lean_dec(v_us_3086_);
lean_dec(v_declName_3085_);
v___x_3159_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
goto v___jp_3111_;
}
}
else
{
lean_object* v_val_3168_; lean_object* v___x_3170_; 
lean_dec(v_a_3107_);
lean_dec(v_us_3086_);
lean_dec(v_declName_3085_);
v_val_3168_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_val_3168_);
lean_dec_ref_known(v___x_3154_, 1);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v_val_3168_);
v___x_3170_ = v___x_3109_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_val_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
v___jp_3111_:
{
lean_object* v___x_3112_; 
v___x_3112_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3085_, v_us_3086_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; uint8_t v___x_3114_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v___x_3114_ = l_Lean_Expr_hasMVar(v_a_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3149_; 
lean_inc(v_a_3113_);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v___x_3112_, 0);
lean_dec(v_unused_3150_);
v___x_3116_ = v___x_3112_;
v_isShared_3117_ = v_isSharedCheck_3149_;
goto v_resetjp_3115_;
}
else
{
lean_dec(v___x_3112_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3149_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v_cache_3119_; lean_object* v_mctx_3120_; lean_object* v_zetaDeltaFVarIds_3121_; lean_object* v_postponed_3122_; lean_object* v_diag_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3148_; 
v___x_3118_ = lean_st_ref_take(v_a_3035_);
v_cache_3119_ = lean_ctor_get(v___x_3118_, 1);
v_mctx_3120_ = lean_ctor_get(v___x_3118_, 0);
v_zetaDeltaFVarIds_3121_ = lean_ctor_get(v___x_3118_, 2);
v_postponed_3122_ = lean_ctor_get(v___x_3118_, 3);
v_diag_3123_ = lean_ctor_get(v___x_3118_, 4);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3125_ = v___x_3118_;
v_isShared_3126_ = v_isSharedCheck_3148_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_diag_3123_);
lean_inc(v_postponed_3122_);
lean_inc(v_zetaDeltaFVarIds_3121_);
lean_inc(v_cache_3119_);
lean_inc(v_mctx_3120_);
lean_dec(v___x_3118_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3148_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v_inferType_3127_; lean_object* v_funInfo_3128_; lean_object* v_synthInstance_3129_; lean_object* v_whnf_3130_; lean_object* v_defEqTrans_3131_; lean_object* v_defEqPerm_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3147_; 
v_inferType_3127_ = lean_ctor_get(v_cache_3119_, 0);
v_funInfo_3128_ = lean_ctor_get(v_cache_3119_, 1);
v_synthInstance_3129_ = lean_ctor_get(v_cache_3119_, 2);
v_whnf_3130_ = lean_ctor_get(v_cache_3119_, 3);
v_defEqTrans_3131_ = lean_ctor_get(v_cache_3119_, 4);
v_defEqPerm_3132_ = lean_ctor_get(v_cache_3119_, 5);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_cache_3119_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3134_ = v_cache_3119_;
v_isShared_3135_ = v_isSharedCheck_3147_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_defEqPerm_3132_);
lean_inc(v_defEqTrans_3131_);
lean_inc(v_whnf_3130_);
lean_inc(v_synthInstance_3129_);
lean_inc(v_funInfo_3128_);
lean_inc(v_inferType_3127_);
lean_dec(v_cache_3119_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3147_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
lean_inc(v_a_3113_);
v___x_3136_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3127_, v_a_3107_, v_a_3113_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_funInfo_3128_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_synthInstance_3129_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_whnf_3130_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v_defEqTrans_3131_);
lean_ctor_set(v_reuseFailAlloc_3146_, 5, v_defEqPerm_3132_);
v___x_3138_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3140_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v___x_3138_);
v___x_3140_ = v___x_3125_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_mctx_3120_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_zetaDeltaFVarIds_3121_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_postponed_3122_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_diag_3123_);
v___x_3140_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = lean_st_ref_put(v_a_3035_, v___x_3140_);
if (v_isShared_3117_ == 0)
{
v___x_3143_ = v___x_3116_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3113_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3107_);
return v___x_3112_;
}
}
else
{
lean_dec(v_a_3107_);
return v___x_3112_;
}
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v_us_3086_);
lean_dec(v_declName_3085_);
v_a_3173_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3106_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3106_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3033_, 2);
goto v___jp_3087_;
}
}
}
v___jp_3087_:
{
lean_object* v_toCold_3088_; lean_object* v_cancelTk_x3f_3089_; 
v_toCold_3088_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3089_ = lean_ctor_get(v_toCold_3088_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3089_) == 1)
{
lean_object* v_val_3090_; uint8_t v___x_3091_; 
v_val_3090_ = lean_ctor_get(v_cancelTk_x3f_3089_, 0);
v___x_3091_ = l_IO_CancelToken_isSet(v_val_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; 
v___x_3092_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3085_, v_us_3086_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3092_;
}
else
{
lean_object* v___x_3093_; lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_us_3086_);
lean_dec(v_declName_3085_);
v___x_3093_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v___x_3102_; 
v___x_3102_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3085_, v_us_3086_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3102_;
}
}
}
case 5:
{
lean_object* v_fn_3181_; uint8_t v_cacheInferType_3182_; lean_object* v_nargs_3183_; lean_object* v___x_3184_; lean_object* v_dummy_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v_fn_3181_ = lean_ctor_get(v_e_3033_, 0);
v_cacheInferType_3182_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*7 + 3);
v_nargs_3183_ = l_Lean_Expr_getAppNumArgs(v_e_3033_);
v___x_3184_ = l_Lean_Expr_getAppFn(v_fn_3181_);
v_dummy_3185_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3183_);
v___x_3186_ = lean_mk_array(v_nargs_3183_, v_dummy_3185_);
v___x_3187_ = lean_unsigned_to_nat(1u);
v___x_3188_ = lean_nat_sub(v_nargs_3183_, v___x_3187_);
lean_dec(v_nargs_3183_);
lean_inc_ref(v_e_3033_);
v___x_3189_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3033_, v___x_3186_, v___x_3188_);
if (v_cacheInferType_3182_ == 0)
{
lean_dec_ref_known(v_e_3033_, 2);
goto v___jp_3190_;
}
else
{
uint8_t v___x_3206_; 
v___x_3206_ = l_Lean_Expr_hasMVar(v_e_3033_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3273_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3210_ = v___x_3207_;
v_isShared_3211_ = v_isSharedCheck_3273_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3207_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3273_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3252_; lean_object* v_cache_3253_; lean_object* v_inferType_3254_; lean_object* v___x_3255_; 
v___x_3252_ = lean_st_ref_get(v_a_3035_);
v_cache_3253_ = lean_ctor_get(v___x_3252_, 1);
lean_inc_ref(v_cache_3253_);
lean_dec(v___x_3252_);
v_inferType_3254_ = lean_ctor_get(v_cache_3253_, 0);
lean_inc_ref(v_inferType_3254_);
lean_dec_ref(v_cache_3253_);
v___x_3255_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3254_, v_a_3208_);
lean_dec_ref(v_inferType_3254_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_toCold_3256_; lean_object* v_cancelTk_x3f_3257_; 
lean_del_object(v___x_3210_);
v_toCold_3256_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3257_ = lean_ctor_get(v_toCold_3256_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3257_) == 1)
{
lean_object* v_val_3258_; uint8_t v___x_3259_; 
v_val_3258_ = lean_ctor_get(v_cancelTk_x3f_3257_, 0);
v___x_3259_ = l_IO_CancelToken_isSet(v_val_3258_);
if (v___x_3259_ == 0)
{
goto v___jp_3212_;
}
else
{
lean_object* v___x_3260_; lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v_a_3208_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v___x_3184_);
v___x_3260_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
else
{
goto v___jp_3212_;
}
}
else
{
lean_object* v_val_3269_; lean_object* v___x_3271_; 
lean_dec(v_a_3208_);
lean_dec_ref(v___x_3189_);
lean_dec_ref(v___x_3184_);
v_val_3269_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_val_3269_);
lean_dec_ref_known(v___x_3255_, 1);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v_val_3269_);
v___x_3271_ = v___x_3210_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_val_3269_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
v___jp_3212_:
{
lean_object* v___x_3213_; 
v___x_3213_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3184_, v___x_3189_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec_ref(v___x_3189_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; uint8_t v___x_3215_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v___x_3215_ = l_Lean_Expr_hasMVar(v_a_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3250_; 
lean_inc(v_a_3214_);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3251_);
v___x_3217_ = v___x_3213_;
v_isShared_3218_ = v_isSharedCheck_3250_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v___x_3213_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3250_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v_cache_3220_; lean_object* v_mctx_3221_; lean_object* v_zetaDeltaFVarIds_3222_; lean_object* v_postponed_3223_; lean_object* v_diag_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3249_; 
v___x_3219_ = lean_st_ref_take(v_a_3035_);
v_cache_3220_ = lean_ctor_get(v___x_3219_, 1);
v_mctx_3221_ = lean_ctor_get(v___x_3219_, 0);
v_zetaDeltaFVarIds_3222_ = lean_ctor_get(v___x_3219_, 2);
v_postponed_3223_ = lean_ctor_get(v___x_3219_, 3);
v_diag_3224_ = lean_ctor_get(v___x_3219_, 4);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3226_ = v___x_3219_;
v_isShared_3227_ = v_isSharedCheck_3249_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_diag_3224_);
lean_inc(v_postponed_3223_);
lean_inc(v_zetaDeltaFVarIds_3222_);
lean_inc(v_cache_3220_);
lean_inc(v_mctx_3221_);
lean_dec(v___x_3219_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3249_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v_inferType_3228_; lean_object* v_funInfo_3229_; lean_object* v_synthInstance_3230_; lean_object* v_whnf_3231_; lean_object* v_defEqTrans_3232_; lean_object* v_defEqPerm_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3248_; 
v_inferType_3228_ = lean_ctor_get(v_cache_3220_, 0);
v_funInfo_3229_ = lean_ctor_get(v_cache_3220_, 1);
v_synthInstance_3230_ = lean_ctor_get(v_cache_3220_, 2);
v_whnf_3231_ = lean_ctor_get(v_cache_3220_, 3);
v_defEqTrans_3232_ = lean_ctor_get(v_cache_3220_, 4);
v_defEqPerm_3233_ = lean_ctor_get(v_cache_3220_, 5);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_cache_3220_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3235_ = v_cache_3220_;
v_isShared_3236_ = v_isSharedCheck_3248_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_defEqPerm_3233_);
lean_inc(v_defEqTrans_3232_);
lean_inc(v_whnf_3231_);
lean_inc(v_synthInstance_3230_);
lean_inc(v_funInfo_3229_);
lean_inc(v_inferType_3228_);
lean_dec(v_cache_3220_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3248_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_inc(v_a_3214_);
v___x_3237_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3228_, v_a_3208_, v_a_3214_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3237_);
v___x_3239_ = v___x_3235_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_funInfo_3229_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_synthInstance_3230_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_whnf_3231_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_defEqTrans_3232_);
lean_ctor_set(v_reuseFailAlloc_3247_, 5, v_defEqPerm_3233_);
v___x_3239_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3241_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 1, v___x_3239_);
v___x_3241_ = v___x_3226_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_mctx_3221_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_zetaDeltaFVarIds_3222_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_postponed_3223_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v_diag_3224_);
v___x_3241_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3242_ = lean_st_ref_put(v_a_3035_, v___x_3241_);
if (v_isShared_3218_ == 0)
{
v___x_3244_ = v___x_3217_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3214_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3208_);
return v___x_3213_;
}
}
else
{
lean_dec(v_a_3208_);
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref(v___x_3189_);
lean_dec_ref(v___x_3184_);
v_a_3274_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3207_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3207_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3033_, 2);
goto v___jp_3190_;
}
}
v___jp_3190_:
{
lean_object* v_toCold_3191_; lean_object* v_cancelTk_x3f_3192_; 
v_toCold_3191_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3192_ = lean_ctor_get(v_toCold_3191_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3192_) == 1)
{
lean_object* v_val_3193_; uint8_t v___x_3194_; 
v_val_3193_ = lean_ctor_get(v_cancelTk_x3f_3192_, 0);
v___x_3194_ = l_IO_CancelToken_isSet(v_val_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
v___x_3195_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3184_, v___x_3189_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec_ref(v___x_3189_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref(v___x_3189_);
lean_dec_ref(v___x_3184_);
v___x_3196_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
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
lean_object* v___x_3205_; 
v___x_3205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3184_, v___x_3189_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec_ref(v___x_3189_);
return v___x_3205_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3282_; 
v_cacheInferType_3282_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3282_ == 0)
{
goto v___jp_3055_;
}
else
{
uint8_t v___x_3283_; 
v___x_3283_ = l_Lean_Expr_hasMVar(v_e_3033_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; 
lean_inc_ref(v_e_3033_);
v___x_3284_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3350_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3350_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3350_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3329_; lean_object* v_cache_3330_; lean_object* v_inferType_3331_; lean_object* v___x_3332_; 
v___x_3329_ = lean_st_ref_get(v_a_3035_);
v_cache_3330_ = lean_ctor_get(v___x_3329_, 1);
lean_inc_ref(v_cache_3330_);
lean_dec(v___x_3329_);
v_inferType_3331_ = lean_ctor_get(v_cache_3330_, 0);
lean_inc_ref(v_inferType_3331_);
lean_dec_ref(v_cache_3330_);
v___x_3332_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3331_, v_a_3285_);
lean_dec_ref(v_inferType_3331_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_toCold_3333_; lean_object* v_cancelTk_x3f_3334_; 
lean_del_object(v___x_3287_);
v_toCold_3333_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3334_ = lean_ctor_get(v_toCold_3333_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3334_) == 1)
{
lean_object* v_val_3335_; uint8_t v___x_3336_; 
v_val_3335_ = lean_ctor_get(v_cancelTk_x3f_3334_, 0);
v___x_3336_ = l_IO_CancelToken_isSet(v_val_3335_);
if (v___x_3336_ == 0)
{
goto v___jp_3289_;
}
else
{
lean_object* v___x_3337_; lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3285_);
lean_dec_ref_known(v_e_3033_, 3);
v___x_3337_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
goto v___jp_3289_;
}
}
else
{
lean_object* v_val_3346_; lean_object* v___x_3348_; 
lean_dec(v_a_3285_);
lean_dec_ref_known(v_e_3033_, 3);
v_val_3346_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_val_3346_);
lean_dec_ref_known(v___x_3332_, 1);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v_val_3346_);
v___x_3348_ = v___x_3287_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_val_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
v___jp_3289_:
{
lean_object* v___x_3290_; 
v___x_3290_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; uint8_t v___x_3292_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v___x_3292_ = l_Lean_Expr_hasMVar(v_a_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3327_; 
lean_inc(v_a_3291_);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v___x_3290_, 0);
lean_dec(v_unused_3328_);
v___x_3294_ = v___x_3290_;
v_isShared_3295_ = v_isSharedCheck_3327_;
goto v_resetjp_3293_;
}
else
{
lean_dec(v___x_3290_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3327_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v_cache_3297_; lean_object* v_mctx_3298_; lean_object* v_zetaDeltaFVarIds_3299_; lean_object* v_postponed_3300_; lean_object* v_diag_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3326_; 
v___x_3296_ = lean_st_ref_take(v_a_3035_);
v_cache_3297_ = lean_ctor_get(v___x_3296_, 1);
v_mctx_3298_ = lean_ctor_get(v___x_3296_, 0);
v_zetaDeltaFVarIds_3299_ = lean_ctor_get(v___x_3296_, 2);
v_postponed_3300_ = lean_ctor_get(v___x_3296_, 3);
v_diag_3301_ = lean_ctor_get(v___x_3296_, 4);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3303_ = v___x_3296_;
v_isShared_3304_ = v_isSharedCheck_3326_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_diag_3301_);
lean_inc(v_postponed_3300_);
lean_inc(v_zetaDeltaFVarIds_3299_);
lean_inc(v_cache_3297_);
lean_inc(v_mctx_3298_);
lean_dec(v___x_3296_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3326_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v_inferType_3305_; lean_object* v_funInfo_3306_; lean_object* v_synthInstance_3307_; lean_object* v_whnf_3308_; lean_object* v_defEqTrans_3309_; lean_object* v_defEqPerm_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3325_; 
v_inferType_3305_ = lean_ctor_get(v_cache_3297_, 0);
v_funInfo_3306_ = lean_ctor_get(v_cache_3297_, 1);
v_synthInstance_3307_ = lean_ctor_get(v_cache_3297_, 2);
v_whnf_3308_ = lean_ctor_get(v_cache_3297_, 3);
v_defEqTrans_3309_ = lean_ctor_get(v_cache_3297_, 4);
v_defEqPerm_3310_ = lean_ctor_get(v_cache_3297_, 5);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_cache_3297_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3312_ = v_cache_3297_;
v_isShared_3313_ = v_isSharedCheck_3325_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_defEqPerm_3310_);
lean_inc(v_defEqTrans_3309_);
lean_inc(v_whnf_3308_);
lean_inc(v_synthInstance_3307_);
lean_inc(v_funInfo_3306_);
lean_inc(v_inferType_3305_);
lean_dec(v_cache_3297_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3325_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
lean_inc(v_a_3291_);
v___x_3314_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3305_, v_a_3285_, v_a_3291_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_funInfo_3306_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_synthInstance_3307_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v_whnf_3308_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v_defEqTrans_3309_);
lean_ctor_set(v_reuseFailAlloc_3324_, 5, v_defEqPerm_3310_);
v___x_3316_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 1, v___x_3316_);
v___x_3318_ = v___x_3303_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_mctx_3298_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3323_, 2, v_zetaDeltaFVarIds_3299_);
lean_ctor_set(v_reuseFailAlloc_3323_, 3, v_postponed_3300_);
lean_ctor_set(v_reuseFailAlloc_3323_, 4, v_diag_3301_);
v___x_3318_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3319_ = lean_st_ref_put(v_a_3035_, v___x_3318_);
if (v_isShared_3295_ == 0)
{
v___x_3321_ = v___x_3294_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3291_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3285_);
return v___x_3290_;
}
}
else
{
lean_dec(v_a_3285_);
return v___x_3290_;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec_ref_known(v_e_3033_, 3);
v_a_3351_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3284_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3284_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
goto v___jp_3055_;
}
}
}
case 9:
{
lean_object* v_a_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v_a_3359_ = lean_ctor_get(v_e_3033_, 0);
lean_inc_ref(v_a_3359_);
lean_dec_ref_known(v_e_3033_, 1);
v___x_3360_ = l_Lean_Literal_type(v_a_3359_);
lean_dec_ref(v_a_3359_);
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
case 10:
{
lean_object* v_expr_3362_; 
v_expr_3362_ = lean_ctor_get(v_e_3033_, 1);
lean_inc_ref(v_expr_3362_);
lean_dec_ref_known(v_e_3033_, 2);
v_e_3033_ = v_expr_3362_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3364_; lean_object* v_idx_3365_; lean_object* v_struct_3366_; uint8_t v_cacheInferType_3383_; 
v_typeName_3364_ = lean_ctor_get(v_e_3033_, 0);
lean_inc(v_typeName_3364_);
v_idx_3365_ = lean_ctor_get(v_e_3033_, 1);
lean_inc(v_idx_3365_);
v_struct_3366_ = lean_ctor_get(v_e_3033_, 2);
lean_inc_ref(v_struct_3366_);
v_cacheInferType_3383_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3383_ == 0)
{
lean_dec_ref_known(v_e_3033_, 3);
goto v___jp_3367_;
}
else
{
uint8_t v___x_3384_; 
v___x_3384_ = l_Lean_Expr_hasMVar(v_e_3033_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3451_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3451_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3451_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3430_; lean_object* v_cache_3431_; lean_object* v_inferType_3432_; lean_object* v___x_3433_; 
v___x_3430_ = lean_st_ref_get(v_a_3035_);
v_cache_3431_ = lean_ctor_get(v___x_3430_, 1);
lean_inc_ref(v_cache_3431_);
lean_dec(v___x_3430_);
v_inferType_3432_ = lean_ctor_get(v_cache_3431_, 0);
lean_inc_ref(v_inferType_3432_);
lean_dec_ref(v_cache_3431_);
v___x_3433_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3432_, v_a_3386_);
lean_dec_ref(v_inferType_3432_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_toCold_3434_; lean_object* v_cancelTk_x3f_3435_; 
lean_del_object(v___x_3388_);
v_toCold_3434_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3435_ = lean_ctor_get(v_toCold_3434_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3435_) == 1)
{
lean_object* v_val_3436_; uint8_t v___x_3437_; 
v_val_3436_ = lean_ctor_get(v_cancelTk_x3f_3435_, 0);
v___x_3437_ = l_IO_CancelToken_isSet(v_val_3436_);
if (v___x_3437_ == 0)
{
goto v___jp_3390_;
}
else
{
lean_object* v___x_3438_; lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_a_3386_);
lean_dec_ref(v_struct_3366_);
lean_dec(v_idx_3365_);
lean_dec(v_typeName_3364_);
v___x_3438_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
goto v___jp_3390_;
}
}
else
{
lean_object* v_val_3447_; lean_object* v___x_3449_; 
lean_dec(v_a_3386_);
lean_dec_ref(v_struct_3366_);
lean_dec(v_idx_3365_);
lean_dec(v_typeName_3364_);
v_val_3447_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_val_3447_);
lean_dec_ref_known(v___x_3433_, 1);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v_val_3447_);
v___x_3449_ = v___x_3388_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_val_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
v___jp_3390_:
{
lean_object* v___x_3391_; 
v___x_3391_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3364_, v_idx_3365_, v_struct_3366_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; uint8_t v___x_3393_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v___x_3393_ = l_Lean_Expr_hasMVar(v_a_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3428_; 
lean_inc(v_a_3392_);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; 
v_unused_3429_ = lean_ctor_get(v___x_3391_, 0);
lean_dec(v_unused_3429_);
v___x_3395_ = v___x_3391_;
v_isShared_3396_ = v_isSharedCheck_3428_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v___x_3391_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3428_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v_cache_3398_; lean_object* v_mctx_3399_; lean_object* v_zetaDeltaFVarIds_3400_; lean_object* v_postponed_3401_; lean_object* v_diag_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3427_; 
v___x_3397_ = lean_st_ref_take(v_a_3035_);
v_cache_3398_ = lean_ctor_get(v___x_3397_, 1);
v_mctx_3399_ = lean_ctor_get(v___x_3397_, 0);
v_zetaDeltaFVarIds_3400_ = lean_ctor_get(v___x_3397_, 2);
v_postponed_3401_ = lean_ctor_get(v___x_3397_, 3);
v_diag_3402_ = lean_ctor_get(v___x_3397_, 4);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3404_ = v___x_3397_;
v_isShared_3405_ = v_isSharedCheck_3427_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_diag_3402_);
lean_inc(v_postponed_3401_);
lean_inc(v_zetaDeltaFVarIds_3400_);
lean_inc(v_cache_3398_);
lean_inc(v_mctx_3399_);
lean_dec(v___x_3397_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3427_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_inferType_3406_; lean_object* v_funInfo_3407_; lean_object* v_synthInstance_3408_; lean_object* v_whnf_3409_; lean_object* v_defEqTrans_3410_; lean_object* v_defEqPerm_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3426_; 
v_inferType_3406_ = lean_ctor_get(v_cache_3398_, 0);
v_funInfo_3407_ = lean_ctor_get(v_cache_3398_, 1);
v_synthInstance_3408_ = lean_ctor_get(v_cache_3398_, 2);
v_whnf_3409_ = lean_ctor_get(v_cache_3398_, 3);
v_defEqTrans_3410_ = lean_ctor_get(v_cache_3398_, 4);
v_defEqPerm_3411_ = lean_ctor_get(v_cache_3398_, 5);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_cache_3398_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3413_ = v_cache_3398_;
v_isShared_3414_ = v_isSharedCheck_3426_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_defEqPerm_3411_);
lean_inc(v_defEqTrans_3410_);
lean_inc(v_whnf_3409_);
lean_inc(v_synthInstance_3408_);
lean_inc(v_funInfo_3407_);
lean_inc(v_inferType_3406_);
lean_dec(v_cache_3398_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3426_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
lean_inc(v_a_3392_);
v___x_3415_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3406_, v_a_3386_, v_a_3392_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_funInfo_3407_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_synthInstance_3408_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_whnf_3409_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_defEqTrans_3410_);
lean_ctor_set(v_reuseFailAlloc_3425_, 5, v_defEqPerm_3411_);
v___x_3417_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v___x_3417_);
v___x_3419_ = v___x_3404_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_mctx_3399_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_zetaDeltaFVarIds_3400_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_postponed_3401_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_diag_3402_);
v___x_3419_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_st_ref_put(v_a_3035_, v___x_3419_);
if (v_isShared_3396_ == 0)
{
v___x_3422_ = v___x_3395_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3392_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3386_);
return v___x_3391_;
}
}
else
{
lean_dec(v_a_3386_);
return v___x_3391_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec_ref(v_struct_3366_);
lean_dec(v_idx_3365_);
lean_dec(v_typeName_3364_);
v_a_3452_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3385_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3385_);
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
lean_dec_ref_known(v_e_3033_, 3);
goto v___jp_3367_;
}
}
v___jp_3367_:
{
lean_object* v_toCold_3368_; lean_object* v_cancelTk_x3f_3369_; 
v_toCold_3368_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3369_ = lean_ctor_get(v_toCold_3368_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3369_) == 1)
{
lean_object* v_val_3370_; uint8_t v___x_3371_; 
v_val_3370_ = lean_ctor_get(v_cancelTk_x3f_3369_, 0);
v___x_3371_ = l_IO_CancelToken_isSet(v_val_3370_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3364_, v_idx_3365_, v_struct_3366_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3372_;
}
else
{
lean_object* v___x_3373_; lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec_ref(v_struct_3366_);
lean_dec(v_idx_3365_);
lean_dec(v_typeName_3364_);
v___x_3373_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3373_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
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
lean_object* v___x_3382_; 
v___x_3382_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3364_, v_idx_3365_, v_struct_3366_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3382_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3460_; 
v_cacheInferType_3460_ = lean_ctor_get_uint8(v_a_3034_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3460_ == 0)
{
goto v___jp_3039_;
}
else
{
uint8_t v___x_3461_; 
v___x_3461_ = l_Lean_Expr_hasMVar(v_e_3033_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
lean_inc_ref(v_e_3033_);
v___x_3462_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3528_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3528_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3528_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3507_; lean_object* v_cache_3508_; lean_object* v_inferType_3509_; lean_object* v___x_3510_; 
v___x_3507_ = lean_st_ref_get(v_a_3035_);
v_cache_3508_ = lean_ctor_get(v___x_3507_, 1);
lean_inc_ref(v_cache_3508_);
lean_dec(v___x_3507_);
v_inferType_3509_ = lean_ctor_get(v_cache_3508_, 0);
lean_inc_ref(v_inferType_3509_);
lean_dec_ref(v_cache_3508_);
v___x_3510_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3509_, v_a_3463_);
lean_dec_ref(v_inferType_3509_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_toCold_3511_; lean_object* v_cancelTk_x3f_3512_; 
lean_del_object(v___x_3465_);
v_toCold_3511_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3512_ = lean_ctor_get(v_toCold_3511_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3512_) == 1)
{
lean_object* v_val_3513_; uint8_t v___x_3514_; 
v_val_3513_ = lean_ctor_get(v_cancelTk_x3f_3512_, 0);
v___x_3514_ = l_IO_CancelToken_isSet(v_val_3513_);
if (v___x_3514_ == 0)
{
goto v___jp_3467_;
}
else
{
lean_object* v___x_3515_; lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec(v_a_3463_);
lean_dec_ref(v_e_3033_);
v___x_3515_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
goto v___jp_3467_;
}
}
else
{
lean_object* v_val_3524_; lean_object* v___x_3526_; 
lean_dec(v_a_3463_);
lean_dec_ref(v_e_3033_);
v_val_3524_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3524_);
lean_dec_ref_known(v___x_3510_, 1);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v_val_3524_);
v___x_3526_ = v___x_3465_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_val_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
v___jp_3467_:
{
lean_object* v___x_3468_; 
v___x_3468_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; uint8_t v___x_3470_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v___x_3470_ = l_Lean_Expr_hasMVar(v_a_3469_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3505_; 
lean_inc(v_a_3469_);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; 
v_unused_3506_ = lean_ctor_get(v___x_3468_, 0);
lean_dec(v_unused_3506_);
v___x_3472_ = v___x_3468_;
v_isShared_3473_ = v_isSharedCheck_3505_;
goto v_resetjp_3471_;
}
else
{
lean_dec(v___x_3468_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3505_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v_cache_3475_; lean_object* v_mctx_3476_; lean_object* v_zetaDeltaFVarIds_3477_; lean_object* v_postponed_3478_; lean_object* v_diag_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3504_; 
v___x_3474_ = lean_st_ref_take(v_a_3035_);
v_cache_3475_ = lean_ctor_get(v___x_3474_, 1);
v_mctx_3476_ = lean_ctor_get(v___x_3474_, 0);
v_zetaDeltaFVarIds_3477_ = lean_ctor_get(v___x_3474_, 2);
v_postponed_3478_ = lean_ctor_get(v___x_3474_, 3);
v_diag_3479_ = lean_ctor_get(v___x_3474_, 4);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3481_ = v___x_3474_;
v_isShared_3482_ = v_isSharedCheck_3504_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_diag_3479_);
lean_inc(v_postponed_3478_);
lean_inc(v_zetaDeltaFVarIds_3477_);
lean_inc(v_cache_3475_);
lean_inc(v_mctx_3476_);
lean_dec(v___x_3474_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3504_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_inferType_3483_; lean_object* v_funInfo_3484_; lean_object* v_synthInstance_3485_; lean_object* v_whnf_3486_; lean_object* v_defEqTrans_3487_; lean_object* v_defEqPerm_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3503_; 
v_inferType_3483_ = lean_ctor_get(v_cache_3475_, 0);
v_funInfo_3484_ = lean_ctor_get(v_cache_3475_, 1);
v_synthInstance_3485_ = lean_ctor_get(v_cache_3475_, 2);
v_whnf_3486_ = lean_ctor_get(v_cache_3475_, 3);
v_defEqTrans_3487_ = lean_ctor_get(v_cache_3475_, 4);
v_defEqPerm_3488_ = lean_ctor_get(v_cache_3475_, 5);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_cache_3475_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3490_ = v_cache_3475_;
v_isShared_3491_ = v_isSharedCheck_3503_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_defEqPerm_3488_);
lean_inc(v_defEqTrans_3487_);
lean_inc(v_whnf_3486_);
lean_inc(v_synthInstance_3485_);
lean_inc(v_funInfo_3484_);
lean_inc(v_inferType_3483_);
lean_dec(v_cache_3475_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3503_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
lean_inc(v_a_3469_);
v___x_3492_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3483_, v_a_3463_, v_a_3469_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3492_);
v___x_3494_ = v___x_3490_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_funInfo_3484_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_synthInstance_3485_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_whnf_3486_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v_defEqTrans_3487_);
lean_ctor_set(v_reuseFailAlloc_3502_, 5, v_defEqPerm_3488_);
v___x_3494_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3496_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___x_3494_);
v___x_3496_ = v___x_3481_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_mctx_3476_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_zetaDeltaFVarIds_3477_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v_postponed_3478_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_diag_3479_);
v___x_3496_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3497_ = lean_st_ref_put(v_a_3035_, v___x_3496_);
if (v_isShared_3473_ == 0)
{
v___x_3499_ = v___x_3472_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3469_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3463_);
return v___x_3468_;
}
}
else
{
lean_dec(v_a_3463_);
return v___x_3468_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v_e_3033_);
v_a_3529_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3462_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3462_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
else
{
goto v___jp_3039_;
}
}
}
}
v___jp_3039_:
{
lean_object* v_toCold_3040_; lean_object* v_cancelTk_x3f_3041_; 
v_toCold_3040_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3041_ = lean_ctor_get(v_toCold_3040_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3041_) == 1)
{
lean_object* v_val_3042_; uint8_t v___x_3043_; 
v_val_3042_ = lean_ctor_get(v_cancelTk_x3f_3041_, 0);
v___x_3043_ = l_IO_CancelToken_isSet(v_val_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3044_;
}
else
{
lean_object* v___x_3045_; lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec_ref(v_e_3033_);
v___x_3045_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v___x_3054_; 
v___x_3054_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3054_;
}
}
v___jp_3055_:
{
lean_object* v_toCold_3056_; lean_object* v_cancelTk_x3f_3057_; 
v_toCold_3056_ = lean_ctor_get(v_a_3036_, 0);
v_cancelTk_x3f_3057_ = lean_ctor_get(v_toCold_3056_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3057_) == 1)
{
lean_object* v_val_3058_; uint8_t v___x_3059_; 
v_val_3058_ = lean_ctor_get(v_cancelTk_x3f_3057_, 0);
v___x_3059_ = l_IO_CancelToken_isSet(v_val_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; 
v___x_3060_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3060_;
}
else
{
lean_object* v___x_3061_; lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec_ref(v_e_3033_);
v___x_3061_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
else
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
return v___x_3070_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3544_, lean_object* v_x_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3545_, v_x_3546_, v_x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3550_, v_x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3553_, lean_object* v_x_3554_, lean_object* v_x_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3553_, v_x_3554_, v_x_3555_);
lean_dec_ref(v_x_3555_);
lean_dec_ref(v_x_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3557_, lean_object* v_x_3558_, size_t v_x_3559_, size_t v_x_3560_, lean_object* v_x_3561_, lean_object* v_x_3562_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3558_, v_x_3559_, v_x_3560_, v_x_3561_, v_x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3564_, lean_object* v_x_3565_, lean_object* v_x_3566_, lean_object* v_x_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_){
_start:
{
size_t v_x_3654__boxed_3570_; size_t v_x_3655__boxed_3571_; lean_object* v_res_3572_; 
v_x_3654__boxed_3570_ = lean_unbox_usize(v_x_3566_);
lean_dec(v_x_3566_);
v_x_3655__boxed_3571_ = lean_unbox_usize(v_x_3567_);
lean_dec(v_x_3567_);
v_res_3572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3564_, v_x_3565_, v_x_3654__boxed_3570_, v_x_3655__boxed_3571_, v_x_3568_, v_x_3569_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3573_, lean_object* v_x_3574_, size_t v_x_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3574_, v_x_3575_, v_x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3578_, lean_object* v_x_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_){
_start:
{
size_t v_x_3671__boxed_3582_; lean_object* v_res_3583_; 
v_x_3671__boxed_3582_ = lean_unbox_usize(v_x_3580_);
lean_dec(v_x_3580_);
v_res_3583_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3578_, v_x_3579_, v_x_3671__boxed_3582_, v_x_3581_);
lean_dec_ref(v_x_3581_);
lean_dec_ref(v_x_3579_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3584_, lean_object* v_n_3585_, lean_object* v_k_3586_, lean_object* v_v_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3585_, v_k_3586_, v_v_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3589_, size_t v_depth_3590_, lean_object* v_keys_3591_, lean_object* v_vals_3592_, lean_object* v_heq_3593_, lean_object* v_i_3594_, lean_object* v_entries_3595_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3590_, v_keys_3591_, v_vals_3592_, v_i_3594_, v_entries_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3597_, lean_object* v_depth_3598_, lean_object* v_keys_3599_, lean_object* v_vals_3600_, lean_object* v_heq_3601_, lean_object* v_i_3602_, lean_object* v_entries_3603_){
_start:
{
size_t v_depth_boxed_3604_; lean_object* v_res_3605_; 
v_depth_boxed_3604_ = lean_unbox_usize(v_depth_3598_);
lean_dec(v_depth_3598_);
v_res_3605_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3597_, v_depth_boxed_3604_, v_keys_3599_, v_vals_3600_, v_heq_3601_, v_i_3602_, v_entries_3603_);
lean_dec_ref(v_vals_3600_);
lean_dec_ref(v_keys_3599_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3606_, lean_object* v_keys_3607_, lean_object* v_vals_3608_, lean_object* v_heq_3609_, lean_object* v_i_3610_, lean_object* v_k_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3607_, v_vals_3608_, v_i_3610_, v_k_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3613_, lean_object* v_keys_3614_, lean_object* v_vals_3615_, lean_object* v_heq_3616_, lean_object* v_i_3617_, lean_object* v_k_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3613_, v_keys_3614_, v_vals_3615_, v_heq_3616_, v_i_3617_, v_k_3618_);
lean_dec_ref(v_k_3618_);
lean_dec_ref(v_vals_3615_);
lean_dec_ref(v_keys_3614_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3620_, lean_object* v_x_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3621_, v_x_3622_, v_x_3623_, v_x_3624_);
return v___x_3625_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = l_Lean_maxRecDepthErrorMessage;
v___x_3632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3634_ = l_Lean_MessageData_ofFormat(v___x_3633_);
return v___x_3634_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3636_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3637_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3636_);
lean_ctor_set(v___x_3637_, 1, v___x_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3638_){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v_ref_3638_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3643_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3646_, lean_object* v_ref_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3647_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3654_, lean_object* v_ref_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3654_, v_ref_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3714_; uint8_t v_beta_3715_; 
v___x_3714_ = l_Lean_Meta_Context_config(v___y_3663_);
v_beta_3715_ = lean_ctor_get_uint8(v___x_3714_, 13);
if (v_beta_3715_ == 0)
{
lean_dec_ref(v___x_3714_);
goto v___jp_3668_;
}
else
{
uint8_t v_iota_3716_; 
v_iota_3716_ = lean_ctor_get_uint8(v___x_3714_, 12);
if (v_iota_3716_ == 0)
{
lean_dec_ref(v___x_3714_);
goto v___jp_3668_;
}
else
{
uint8_t v_zeta_3717_; 
v_zeta_3717_ = lean_ctor_get_uint8(v___x_3714_, 15);
if (v_zeta_3717_ == 0)
{
lean_dec_ref(v___x_3714_);
goto v___jp_3668_;
}
else
{
uint8_t v_zetaHave_3718_; 
v_zetaHave_3718_ = lean_ctor_get_uint8(v___x_3714_, 18);
if (v_zetaHave_3718_ == 0)
{
lean_dec_ref(v___x_3714_);
goto v___jp_3668_;
}
else
{
uint8_t v_zetaDelta_3719_; 
v_zetaDelta_3719_ = lean_ctor_get_uint8(v___x_3714_, 16);
if (v_zetaDelta_3719_ == 0)
{
lean_dec_ref(v___x_3714_);
goto v___jp_3668_;
}
else
{
uint8_t v_etaStruct_3720_; uint8_t v_proj_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v_etaStruct_3720_ = lean_ctor_get_uint8(v___x_3714_, 10);
v_proj_3721_ = lean_ctor_get_uint8(v___x_3714_, 14);
lean_dec_ref(v___x_3714_);
v___x_3722_ = lean_box(v_proj_3721_);
v___x_3723_ = lean_obj_tag_nat(v___x_3722_);
lean_dec(v___x_3722_);
v___x_3724_ = lean_unsigned_to_nat(2u);
v___x_3725_ = lean_nat_dec_eq(v___x_3723_, v___x_3724_);
if (v___x_3725_ == 0)
{
goto v___jp_3668_;
}
else
{
uint8_t v___x_3726_; uint8_t v___x_3727_; 
v___x_3726_ = 0;
v___x_3727_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3720_, v___x_3726_);
if (v___x_3727_ == 0)
{
goto v___jp_3668_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec_ref(v___y_3663_);
return v___x_3728_;
}
}
}
}
}
}
}
v___jp_3668_:
{
lean_object* v___x_3669_; uint8_t v_foApprox_3670_; uint8_t v_ctxApprox_3671_; uint8_t v_quasiPatternApprox_3672_; uint8_t v_constApprox_3673_; uint8_t v_isDefEqStuckEx_3674_; uint8_t v_unificationHints_3675_; uint8_t v_proofIrrelevance_3676_; uint8_t v_assignSyntheticOpaque_3677_; uint8_t v_offsetCnstrs_3678_; uint8_t v_transparency_3679_; uint8_t v_univApprox_3680_; uint8_t v_zetaUnused_3681_; uint8_t v_canUnfoldPredicateConfig_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3713_; 
v___x_3669_ = l_Lean_Meta_Context_config(v___y_3663_);
v_foApprox_3670_ = lean_ctor_get_uint8(v___x_3669_, 0);
v_ctxApprox_3671_ = lean_ctor_get_uint8(v___x_3669_, 1);
v_quasiPatternApprox_3672_ = lean_ctor_get_uint8(v___x_3669_, 2);
v_constApprox_3673_ = lean_ctor_get_uint8(v___x_3669_, 3);
v_isDefEqStuckEx_3674_ = lean_ctor_get_uint8(v___x_3669_, 4);
v_unificationHints_3675_ = lean_ctor_get_uint8(v___x_3669_, 5);
v_proofIrrelevance_3676_ = lean_ctor_get_uint8(v___x_3669_, 6);
v_assignSyntheticOpaque_3677_ = lean_ctor_get_uint8(v___x_3669_, 7);
v_offsetCnstrs_3678_ = lean_ctor_get_uint8(v___x_3669_, 8);
v_transparency_3679_ = lean_ctor_get_uint8(v___x_3669_, 9);
v_univApprox_3680_ = lean_ctor_get_uint8(v___x_3669_, 11);
v_zetaUnused_3681_ = lean_ctor_get_uint8(v___x_3669_, 17);
v_canUnfoldPredicateConfig_3682_ = lean_ctor_get_uint8(v___x_3669_, 19);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3684_ = v___x_3669_;
v_isShared_3685_ = v_isSharedCheck_3713_;
goto v_resetjp_3683_;
}
else
{
lean_dec(v___x_3669_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3713_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
uint8_t v___x_3686_; uint8_t v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3690_; 
v___x_3686_ = 1;
v___x_3687_ = 0;
v___x_3688_ = 2;
if (v_isShared_3685_ == 0)
{
v___x_3690_ = v___x_3684_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 0, v_foApprox_3670_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 1, v_ctxApprox_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 2, v_quasiPatternApprox_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 3, v_constApprox_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 4, v_isDefEqStuckEx_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 5, v_unificationHints_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 6, v_proofIrrelevance_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 7, v_assignSyntheticOpaque_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 8, v_offsetCnstrs_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 9, v_transparency_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 11, v_univApprox_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 17, v_zetaUnused_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3712_, 19, v_canUnfoldPredicateConfig_3682_);
v___x_3690_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
uint8_t v_trackZetaDelta_3691_; lean_object* v_zetaDeltaSet_3692_; lean_object* v_lctx_3693_; lean_object* v_localInstances_3694_; lean_object* v_defEqCtx_x3f_3695_; lean_object* v_synthPendingDepth_3696_; lean_object* v_customCanUnfoldPredicate_x3f_3697_; uint8_t v_univApprox_3698_; uint8_t v_inTypeClassResolution_3699_; uint8_t v_cacheInferType_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3710_; 
lean_ctor_set_uint8(v___x_3690_, 10, v___x_3687_);
lean_ctor_set_uint8(v___x_3690_, 12, v___x_3686_);
lean_ctor_set_uint8(v___x_3690_, 13, v___x_3686_);
lean_ctor_set_uint8(v___x_3690_, 14, v___x_3688_);
lean_ctor_set_uint8(v___x_3690_, 15, v___x_3686_);
lean_ctor_set_uint8(v___x_3690_, 16, v___x_3686_);
lean_ctor_set_uint8(v___x_3690_, 18, v___x_3686_);
v_trackZetaDelta_3691_ = lean_ctor_get_uint8(v___y_3663_, sizeof(void*)*7);
v_zetaDeltaSet_3692_ = lean_ctor_get(v___y_3663_, 1);
v_lctx_3693_ = lean_ctor_get(v___y_3663_, 2);
v_localInstances_3694_ = lean_ctor_get(v___y_3663_, 3);
v_defEqCtx_x3f_3695_ = lean_ctor_get(v___y_3663_, 4);
v_synthPendingDepth_3696_ = lean_ctor_get(v___y_3663_, 5);
v_customCanUnfoldPredicate_x3f_3697_ = lean_ctor_get(v___y_3663_, 6);
v_univApprox_3698_ = lean_ctor_get_uint8(v___y_3663_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3699_ = lean_ctor_get_uint8(v___y_3663_, sizeof(void*)*7 + 2);
v_cacheInferType_3700_ = lean_ctor_get_uint8(v___y_3663_, sizeof(void*)*7 + 3);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___y_3663_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v___y_3663_, 0);
lean_dec(v_unused_3711_);
v___x_3702_ = v___y_3663_;
v_isShared_3703_ = v_isSharedCheck_3710_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3697_);
lean_inc(v_synthPendingDepth_3696_);
lean_inc(v_defEqCtx_x3f_3695_);
lean_inc(v_localInstances_3694_);
lean_inc(v_lctx_3693_);
lean_inc(v_zetaDeltaSet_3692_);
lean_dec(v___y_3663_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3710_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
uint64_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
v___x_3704_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3690_);
v___x_3705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3705_, 0, v___x_3690_);
lean_ctor_set_uint64(v___x_3705_, sizeof(void*)*1, v___x_3704_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3705_);
v___x_3707_ = v___x_3702_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_zetaDeltaSet_3692_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v_lctx_3693_);
lean_ctor_set(v_reuseFailAlloc_3709_, 3, v_localInstances_3694_);
lean_ctor_set(v_reuseFailAlloc_3709_, 4, v_defEqCtx_x3f_3695_);
lean_ctor_set(v_reuseFailAlloc_3709_, 5, v_synthPendingDepth_3696_);
lean_ctor_set(v_reuseFailAlloc_3709_, 6, v_customCanUnfoldPredicate_x3f_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3709_, sizeof(void*)*7, v_trackZetaDelta_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3709_, sizeof(void*)*7 + 1, v_univApprox_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3709_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3709_, sizeof(void*)*7 + 3, v_cacheInferType_3700_);
v___x_3707_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3662_, v___x_3707_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec_ref(v___x_3707_);
return v___x_3708_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v___y_3743_; lean_object* v_toCold_3760_; lean_object* v_currRecDepth_3761_; lean_object* v_ref_3762_; uint16_t v_optionFlags_3763_; uint8_t v_suppressElabErrors_3764_; uint8_t v_isRecordingDeps_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3805_; 
v_toCold_3760_ = lean_ctor_get(v_a_3739_, 0);
v_currRecDepth_3761_ = lean_ctor_get(v_a_3739_, 1);
v_ref_3762_ = lean_ctor_get(v_a_3739_, 2);
v_optionFlags_3763_ = lean_ctor_get_uint16(v_a_3739_, sizeof(void*)*3);
v_suppressElabErrors_3764_ = lean_ctor_get_uint8(v_a_3739_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3765_ = lean_ctor_get_uint8(v_a_3739_, sizeof(void*)*3 + 3);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_a_3739_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3767_ = v_a_3739_;
v_isShared_3768_ = v_isSharedCheck_3805_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_ref_3762_);
lean_inc(v_currRecDepth_3761_);
lean_inc(v_toCold_3760_);
lean_dec(v_a_3739_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3805_;
goto v_resetjp_3766_;
}
v___jp_3742_:
{
if (lean_obj_tag(v___y_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
v_a_3744_ = lean_ctor_get(v___y_3743_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___y_3743_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___y_3743_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___y_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_a_3752_ = lean_ctor_get(v___y_3743_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___y_3743_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___y_3743_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___y_3743_);
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
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
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
}
v_resetjp_3766_:
{
lean_object* v_maxRecDepth_3769_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v_maxRecDepth_3769_ = lean_ctor_get(v_toCold_3760_, 3);
v___x_3801_ = lean_unsigned_to_nat(0u);
v___x_3802_ = lean_nat_dec_eq(v_maxRecDepth_3769_, v___x_3801_);
if (v___x_3802_ == 0)
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_nat_dec_eq(v_currRecDepth_3761_, v_maxRecDepth_3769_);
if (v___x_3803_ == 0)
{
goto v___jp_3770_;
}
else
{
lean_object* v___x_3804_; 
lean_del_object(v___x_3767_);
lean_dec(v_currRecDepth_3761_);
lean_dec_ref(v_toCold_3760_);
lean_dec(v_a_3740_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec_ref(v_e_3736_);
v___x_3804_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3762_);
return v___x_3804_;
}
}
else
{
goto v___jp_3770_;
}
v___jp_3770_:
{
lean_object* v___x_3771_; uint8_t v_transparency_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3771_ = l_Lean_Meta_Context_config(v_a_3737_);
v_transparency_3772_ = lean_ctor_get_uint8(v___x_3771_, 9);
lean_dec_ref(v___x_3771_);
v___x_3773_ = lean_unsigned_to_nat(1u);
v___x_3774_ = lean_nat_add(v_currRecDepth_3761_, v___x_3773_);
lean_dec(v_currRecDepth_3761_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v___x_3774_);
v___x_3776_ = v___x_3767_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_toCold_3760_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_ref_3762_);
lean_ctor_set_uint16(v_reuseFailAlloc_3800_, sizeof(void*)*3, v_optionFlags_3763_);
lean_ctor_set_uint8(v_reuseFailAlloc_3800_, sizeof(void*)*3 + 2, v_suppressElabErrors_3764_);
lean_ctor_set_uint8(v_reuseFailAlloc_3800_, sizeof(void*)*3 + 3, v_isRecordingDeps_3765_);
v___x_3776_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
uint8_t v___x_3777_; uint8_t v___x_3778_; 
v___x_3777_ = 1;
v___x_3778_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3772_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3736_, v_a_3737_, v_a_3738_, v___x_3776_, v_a_3740_);
lean_dec(v_a_3740_);
lean_dec_ref(v___x_3776_);
lean_dec(v_a_3738_);
v___y_3743_ = v___x_3779_;
goto v___jp_3742_;
}
else
{
lean_object* v_keyedConfig_3780_; uint8_t v_trackZetaDelta_3781_; lean_object* v_zetaDeltaSet_3782_; lean_object* v_lctx_3783_; lean_object* v_localInstances_3784_; lean_object* v_defEqCtx_x3f_3785_; lean_object* v_synthPendingDepth_3786_; lean_object* v_customCanUnfoldPredicate_x3f_3787_; uint8_t v_univApprox_3788_; uint8_t v_inTypeClassResolution_3789_; uint8_t v_cacheInferType_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3799_; 
v_keyedConfig_3780_ = lean_ctor_get(v_a_3737_, 0);
v_trackZetaDelta_3781_ = lean_ctor_get_uint8(v_a_3737_, sizeof(void*)*7);
v_zetaDeltaSet_3782_ = lean_ctor_get(v_a_3737_, 1);
v_lctx_3783_ = lean_ctor_get(v_a_3737_, 2);
v_localInstances_3784_ = lean_ctor_get(v_a_3737_, 3);
v_defEqCtx_x3f_3785_ = lean_ctor_get(v_a_3737_, 4);
v_synthPendingDepth_3786_ = lean_ctor_get(v_a_3737_, 5);
v_customCanUnfoldPredicate_x3f_3787_ = lean_ctor_get(v_a_3737_, 6);
v_univApprox_3788_ = lean_ctor_get_uint8(v_a_3737_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3789_ = lean_ctor_get_uint8(v_a_3737_, sizeof(void*)*7 + 2);
v_cacheInferType_3790_ = lean_ctor_get_uint8(v_a_3737_, sizeof(void*)*7 + 3);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_a_3737_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3792_ = v_a_3737_;
v_isShared_3793_ = v_isSharedCheck_3799_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3787_);
lean_inc(v_synthPendingDepth_3786_);
lean_inc(v_defEqCtx_x3f_3785_);
lean_inc(v_localInstances_3784_);
lean_inc(v_lctx_3783_);
lean_inc(v_zetaDeltaSet_3782_);
lean_inc(v_keyedConfig_3780_);
lean_dec(v_a_3737_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3799_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; lean_object* v___x_3796_; 
v___x_3794_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3777_, v_keyedConfig_3780_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3794_);
v___x_3796_ = v___x_3792_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3794_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_zetaDeltaSet_3782_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_lctx_3783_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_localInstances_3784_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v_defEqCtx_x3f_3785_);
lean_ctor_set(v_reuseFailAlloc_3798_, 5, v_synthPendingDepth_3786_);
lean_ctor_set(v_reuseFailAlloc_3798_, 6, v_customCanUnfoldPredicate_x3f_3787_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, sizeof(void*)*7, v_trackZetaDelta_3781_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, sizeof(void*)*7 + 1, v_univApprox_3788_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3789_);
lean_ctor_set_uint8(v_reuseFailAlloc_3798_, sizeof(void*)*7 + 3, v_cacheInferType_3790_);
v___x_3796_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3736_, v___x_3796_, v_a_3738_, v___x_3776_, v_a_3740_);
lean_dec(v_a_3740_);
lean_dec_ref(v___x_3776_);
lean_dec(v_a_3738_);
v___y_3743_ = v___x_3797_;
goto v___jp_3742_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = lean_infer_type(v_e_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
return v_res_3812_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3813_){
_start:
{
switch(lean_obj_tag(v_x_3813_))
{
case 0:
{
uint8_t v___x_3814_; 
v___x_3814_ = 1;
return v___x_3814_;
}
case 2:
{
lean_object* v_a_3815_; lean_object* v_a_3816_; uint8_t v___x_3817_; 
v_a_3815_ = lean_ctor_get(v_x_3813_, 0);
v_a_3816_ = lean_ctor_get(v_x_3813_, 1);
v___x_3817_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3815_);
if (v___x_3817_ == 0)
{
return v___x_3817_;
}
else
{
v_x_3813_ = v_a_3816_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3819_; 
v_a_3819_ = lean_ctor_get(v_x_3813_, 1);
v_x_3813_ = v_a_3819_;
goto _start;
}
default: 
{
uint8_t v___x_3821_; 
v___x_3821_ = 0;
return v___x_3821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3822_){
_start:
{
uint8_t v_res_3823_; lean_object* v_r_3824_; 
v_res_3823_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3822_);
lean_dec(v_x_3822_);
v_r_3824_ = lean_box(v_res_3823_);
return v_r_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v___x_3828_; lean_object* v_mctx_3829_; lean_object* v___x_3830_; lean_object* v_fst_3831_; lean_object* v_snd_3832_; lean_object* v___x_3833_; lean_object* v_cache_3834_; lean_object* v_zetaDeltaFVarIds_3835_; lean_object* v_postponed_3836_; lean_object* v_diag_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3846_; 
v___x_3828_ = lean_st_ref_get(v___y_3826_);
v_mctx_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc_ref(v_mctx_3829_);
lean_dec(v___x_3828_);
v___x_3830_ = lean_instantiate_level_mvars(v_mctx_3829_, v_l_3825_);
v_fst_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_fst_3831_);
v_snd_3832_ = lean_ctor_get(v___x_3830_, 1);
lean_inc(v_snd_3832_);
lean_dec_ref(v___x_3830_);
v___x_3833_ = lean_st_ref_take(v___y_3826_);
v_cache_3834_ = lean_ctor_get(v___x_3833_, 1);
v_zetaDeltaFVarIds_3835_ = lean_ctor_get(v___x_3833_, 2);
v_postponed_3836_ = lean_ctor_get(v___x_3833_, 3);
v_diag_3837_ = lean_ctor_get(v___x_3833_, 4);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; 
v_unused_3847_ = lean_ctor_get(v___x_3833_, 0);
lean_dec(v_unused_3847_);
v___x_3839_ = v___x_3833_;
v_isShared_3840_ = v_isSharedCheck_3846_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_diag_3837_);
lean_inc(v_postponed_3836_);
lean_inc(v_zetaDeltaFVarIds_3835_);
lean_inc(v_cache_3834_);
lean_dec(v___x_3833_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3846_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_fst_3831_);
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_fst_3831_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_cache_3834_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_zetaDeltaFVarIds_3835_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_postponed_3836_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_diag_3837_);
v___x_3842_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = lean_st_ref_put(v___y_3826_, v___x_3842_);
v___x_3844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3844_, 0, v_snd_3832_);
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3848_, v___y_3849_);
lean_dec(v___y_3849_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3852_, v___y_3854_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3866_, lean_object* v_x_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
switch(lean_obj_tag(v_x_3866_))
{
case 3:
{
lean_object* v_u_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v_u_3877_ = lean_ctor_get(v_x_3866_, 0);
lean_inc(v_u_3877_);
lean_dec_ref_known(v_x_3866_, 1);
v___x_3878_ = lean_unsigned_to_nat(0u);
v___x_3879_ = lean_nat_dec_eq(v_x_3867_, v___x_3878_);
lean_dec(v_x_3867_);
if (v___x_3879_ == 0)
{
lean_dec(v_u_3877_);
goto v___jp_3873_;
}
else
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3877_, v_a_3869_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3891_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3883_ = v___x_3880_;
v_isShared_3884_ = v_isSharedCheck_3891_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3880_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3891_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
uint8_t v___x_3885_; uint8_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3885_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3881_);
lean_dec(v_a_3881_);
v___x_3886_ = l_Lean_Bool_toLBool(v___x_3885_);
v___x_3887_ = lean_box(v___x_3886_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v___x_3887_);
v___x_3889_ = v___x_3883_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
v_a_3892_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3880_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3880_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3900_; lean_object* v_zero_3901_; uint8_t v_isZero_3902_; 
v_body_3900_ = lean_ctor_get(v_x_3866_, 2);
lean_inc_ref(v_body_3900_);
lean_dec_ref_known(v_x_3866_, 3);
v_zero_3901_ = lean_unsigned_to_nat(0u);
v_isZero_3902_ = lean_nat_dec_eq(v_x_3867_, v_zero_3901_);
if (v_isZero_3902_ == 1)
{
uint8_t v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_dec_ref(v_body_3900_);
lean_dec(v_x_3867_);
v___x_3903_ = 0;
v___x_3904_ = lean_box(v___x_3903_);
v___x_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
return v___x_3905_;
}
else
{
lean_object* v_one_3906_; lean_object* v_n_3907_; 
v_one_3906_ = lean_unsigned_to_nat(1u);
v_n_3907_ = lean_nat_sub(v_x_3867_, v_one_3906_);
lean_dec(v_x_3867_);
v_x_3866_ = v_body_3900_;
v_x_3867_ = v_n_3907_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3909_; 
v_body_3909_ = lean_ctor_get(v_x_3866_, 3);
lean_inc_ref(v_body_3909_);
lean_dec_ref_known(v_x_3866_, 4);
v_x_3866_ = v_body_3909_;
goto _start;
}
case 10:
{
lean_object* v_expr_3911_; 
v_expr_3911_ = lean_ctor_get(v_x_3866_, 1);
lean_inc_ref(v_expr_3911_);
lean_dec_ref_known(v_x_3866_, 2);
v_x_3866_ = v_expr_3911_;
goto _start;
}
default: 
{
lean_dec(v_x_3867_);
lean_dec_ref(v_x_3866_);
goto v___jp_3873_;
}
}
v___jp_3873_:
{
uint8_t v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3874_ = 2;
v___x_3875_ = lean_box(v___x_3874_);
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
return v___x_3876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3913_, lean_object* v_x_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3913_, v_x_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
lean_dec(v_a_3918_);
lean_dec_ref(v_a_3917_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3921_, lean_object* v_x_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
switch(lean_obj_tag(v_x_3921_))
{
case 4:
{
lean_object* v_declName_3928_; lean_object* v_us_3929_; lean_object* v___x_3930_; 
v_declName_3928_ = lean_ctor_get(v_x_3921_, 0);
lean_inc(v_declName_3928_);
v_us_3929_ = lean_ctor_get(v_x_3921_, 1);
lean_inc(v_us_3929_);
lean_dec_ref_known(v_x_3921_, 2);
v___x_3930_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3928_, v_us_3929_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3932_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3930_, 1);
v___x_3932_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3931_, v_x_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_3932_;
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec(v_x_3922_);
v_a_3933_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3930_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3930_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3941_; lean_object* v___x_3942_; 
v_fvarId_3941_ = lean_ctor_get(v_x_3921_, 0);
lean_inc(v_fvarId_3941_);
lean_dec_ref_known(v_x_3921_, 1);
v___x_3942_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3941_, v_a_3923_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3944_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v___x_3944_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3943_, v_x_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_3944_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_x_3922_);
v_a_3945_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3942_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3942_);
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
case 2:
{
lean_object* v_mvarId_3953_; lean_object* v___x_3954_; 
v_mvarId_3953_ = lean_ctor_get(v_x_3921_, 0);
lean_inc(v_mvarId_3953_);
lean_dec_ref_known(v_x_3921_, 1);
v___x_3954_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3953_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3955_, v_x_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
return v___x_3956_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_x_3922_);
v_a_3957_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3954_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3954_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
case 5:
{
lean_object* v_fn_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v_fn_3965_ = lean_ctor_get(v_x_3921_, 0);
lean_inc_ref(v_fn_3965_);
lean_dec_ref_known(v_x_3921_, 2);
v___x_3966_ = lean_unsigned_to_nat(1u);
v___x_3967_ = lean_nat_add(v_x_3922_, v___x_3966_);
lean_dec(v_x_3922_);
v_x_3921_ = v_fn_3965_;
v_x_3922_ = v___x_3967_;
goto _start;
}
case 10:
{
lean_object* v_expr_3969_; 
v_expr_3969_ = lean_ctor_get(v_x_3921_, 1);
lean_inc_ref(v_expr_3969_);
lean_dec_ref_known(v_x_3921_, 2);
v_x_3921_ = v_expr_3969_;
goto _start;
}
case 8:
{
lean_object* v_body_3971_; 
v_body_3971_ = lean_ctor_get(v_x_3921_, 3);
lean_inc_ref(v_body_3971_);
lean_dec_ref_known(v_x_3921_, 4);
v_x_3921_ = v_body_3971_;
goto _start;
}
case 6:
{
lean_object* v_body_3973_; lean_object* v_zero_3974_; uint8_t v_isZero_3975_; 
v_body_3973_ = lean_ctor_get(v_x_3921_, 2);
lean_inc_ref(v_body_3973_);
lean_dec_ref_known(v_x_3921_, 3);
v_zero_3974_ = lean_unsigned_to_nat(0u);
v_isZero_3975_ = lean_nat_dec_eq(v_x_3922_, v_zero_3974_);
if (v_isZero_3975_ == 1)
{
uint8_t v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec_ref(v_body_3973_);
lean_dec(v_x_3922_);
v___x_3976_ = 0;
v___x_3977_ = lean_box(v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
return v___x_3978_;
}
else
{
lean_object* v_one_3979_; lean_object* v_n_3980_; 
v_one_3979_ = lean_unsigned_to_nat(1u);
v_n_3980_ = lean_nat_sub(v_x_3922_, v_one_3979_);
lean_dec(v_x_3922_);
v_x_3921_ = v_body_3973_;
v_x_3922_ = v_n_3980_;
goto _start;
}
}
default: 
{
uint8_t v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3921_);
v___x_3982_ = 2;
v___x_3983_ = lean_box(v___x_3982_);
v___x_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
return v___x_3984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3985_, lean_object* v_x_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3985_, v_x_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
switch(lean_obj_tag(v_x_3993_))
{
case 1:
{
lean_object* v_fvarId_3999_; lean_object* v___x_4000_; 
v_fvarId_3999_ = lean_ctor_get(v_x_3993_, 0);
lean_inc(v_fvarId_3999_);
lean_dec_ref_known(v_x_3993_, 1);
v___x_4000_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3999_, v_a_3994_, v_a_3996_, v_a_3997_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v___x_4002_ = lean_unsigned_to_nat(0u);
v___x_4003_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4001_, v___x_4002_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
return v___x_4003_;
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
v_a_4004_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_4000_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_4000_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4012_; lean_object* v___x_4013_; 
v_mvarId_4012_ = lean_ctor_get(v_x_3993_, 0);
lean_inc(v_mvarId_4012_);
lean_dec_ref_known(v_x_3993_, 1);
v___x_4013_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4012_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v___x_4013_, 1);
v___x_4015_ = lean_unsigned_to_nat(0u);
v___x_4016_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4014_, v___x_4015_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
return v___x_4016_;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
v_a_4017_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4013_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4013_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
case 3:
{
uint8_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
lean_dec_ref_known(v_x_3993_, 1);
v___x_4025_ = 0;
v___x_4026_ = lean_box(v___x_4025_);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
case 4:
{
lean_object* v_declName_4028_; lean_object* v_us_4029_; lean_object* v___x_4030_; 
v_declName_4028_ = lean_ctor_get(v_x_3993_, 0);
lean_inc(v_declName_4028_);
v_us_4029_ = lean_ctor_get(v_x_3993_, 1);
lean_inc(v_us_4029_);
lean_dec_ref_known(v_x_3993_, 2);
v___x_4030_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4028_, v_us_4029_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v___x_4032_ = lean_unsigned_to_nat(0u);
v___x_4033_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4031_, v___x_4032_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
return v___x_4033_;
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4030_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4030_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
case 5:
{
lean_object* v_fn_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v_fn_4042_ = lean_ctor_get(v_x_3993_, 0);
lean_inc_ref(v_fn_4042_);
lean_dec_ref_known(v_x_3993_, 2);
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4044_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4042_, v___x_4043_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
return v___x_4044_;
}
case 6:
{
uint8_t v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec_ref_known(v_x_3993_, 3);
v___x_4045_ = 0;
v___x_4046_ = lean_box(v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
case 7:
{
lean_object* v_body_4048_; 
v_body_4048_ = lean_ctor_get(v_x_3993_, 2);
lean_inc_ref(v_body_4048_);
lean_dec_ref_known(v_x_3993_, 3);
v_x_3993_ = v_body_4048_;
goto _start;
}
case 8:
{
lean_object* v_body_4050_; 
v_body_4050_ = lean_ctor_get(v_x_3993_, 3);
lean_inc_ref(v_body_4050_);
lean_dec_ref_known(v_x_3993_, 4);
v_x_3993_ = v_body_4050_;
goto _start;
}
case 9:
{
uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_dec_ref_known(v_x_3993_, 1);
v___x_4052_ = 0;
v___x_4053_ = lean_box(v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
return v___x_4054_;
}
case 10:
{
lean_object* v_expr_4055_; 
v_expr_4055_ = lean_ctor_get(v_x_3993_, 1);
lean_inc_ref(v_expr_4055_);
lean_dec_ref_known(v_x_3993_, 2);
v_x_3993_ = v_expr_4055_;
goto _start;
}
default: 
{
uint8_t v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_dec_ref(v_x_3993_);
v___x_4057_ = 2;
v___x_4058_ = lean_box(v___x_4057_);
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
return v___x_4059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Meta_isPropQuick(v_x_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v___x_4073_; 
lean_inc_ref(v_e_4067_);
v___x_4073_ = l_Lean_Meta_isPropQuick(v_e_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4130_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4130_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4130_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
uint8_t v___x_4078_; 
v___x_4078_ = lean_unbox(v_a_4074_);
lean_dec(v_a_4074_);
switch(v___x_4078_)
{
case 0:
{
uint8_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4082_; 
lean_dec_ref(v_e_4067_);
v___x_4079_ = 0;
v___x_4080_ = lean_box(v___x_4079_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4080_);
v___x_4082_ = v___x_4076_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4080_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
case 1:
{
uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
lean_dec_ref(v_e_4067_);
v___x_4084_ = 1;
v___x_4085_ = lean_box(v___x_4084_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4085_);
v___x_4087_ = v___x_4076_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
default: 
{
lean_object* v___x_4089_; 
lean_del_object(v___x_4076_);
lean_inc(v_a_4071_);
lean_inc_ref(v_a_4070_);
lean_inc(v_a_4069_);
lean_inc_ref(v_a_4068_);
v___x_4089_ = lean_infer_type(v_e_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4091_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4091_ = l_Lean_Meta_whnfD(v_a_4090_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4113_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4113_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4113_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
if (lean_obj_tag(v_a_4092_) == 3)
{
lean_object* v_u_4096_; lean_object* v___x_4097_; lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4107_; 
lean_del_object(v___x_4094_);
v_u_4096_ = lean_ctor_get(v_a_4092_, 0);
lean_inc(v_u_4096_);
lean_dec_ref_known(v_a_4092_, 1);
v___x_4097_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4096_, v_a_4069_);
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4107_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4107_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
uint8_t v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
v___x_4102_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4098_);
lean_dec(v_a_4098_);
v___x_4103_ = lean_box(v___x_4102_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4103_);
v___x_4105_ = v___x_4100_;
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
}
else
{
uint8_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
lean_dec(v_a_4092_);
v___x_4108_ = 0;
v___x_4109_ = lean_box(v___x_4108_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 0, v___x_4109_);
v___x_4111_ = v___x_4094_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
v_a_4114_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4091_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4091_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
v_a_4122_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4089_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4089_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec_ref(v_e_4067_);
v_a_4131_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4073_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4073_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_Meta_isProp(v_e_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4146_){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = lean_obj_tag_nat(v_x_4146_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4148_);
lean_dec(v_x_4148_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4150_, lean_object* v_k_4151_){
_start:
{
if (lean_obj_tag(v_t_4150_) == 3)
{
lean_object* v_idx_4152_; lean_object* v_numArgs_4153_; lean_object* v___x_4154_; 
v_idx_4152_ = lean_ctor_get(v_t_4150_, 0);
lean_inc(v_idx_4152_);
v_numArgs_4153_ = lean_ctor_get(v_t_4150_, 1);
lean_inc(v_numArgs_4153_);
lean_dec_ref_known(v_t_4150_, 2);
v___x_4154_ = lean_apply_2(v_k_4151_, v_idx_4152_, v_numArgs_4153_);
return v___x_4154_;
}
else
{
lean_dec(v_t_4150_);
return v_k_4151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4155_, lean_object* v_ctorIdx_4156_, lean_object* v_t_4157_, lean_object* v_h_4158_, lean_object* v_k_4159_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4157_, v_k_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4161_, lean_object* v_ctorIdx_4162_, lean_object* v_t_4163_, lean_object* v_h_4164_, lean_object* v_k_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4161_, v_ctorIdx_4162_, v_t_4163_, v_h_4164_, v_k_4165_);
lean_dec(v_ctorIdx_4162_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4167_, lean_object* v_false_4168_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4167_, v_false_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4170_, lean_object* v_t_4171_, lean_object* v_h_4172_, lean_object* v_false_4173_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4171_, v_false_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4175_, lean_object* v_true_4176_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4175_, v_true_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4178_, lean_object* v_t_4179_, lean_object* v_h_4180_, lean_object* v_true_4181_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4179_, v_true_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4183_, lean_object* v_undef_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4183_, v_undef_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4186_, lean_object* v_t_4187_, lean_object* v_h_4188_, lean_object* v_undef_4189_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4187_, v_undef_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4191_, lean_object* v_bvar_4192_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4191_, v_bvar_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4194_, lean_object* v_t_4195_, lean_object* v_h_4196_, lean_object* v_bvar_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4195_, v_bvar_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4199_){
_start:
{
switch(v_x_4199_)
{
case 0:
{
lean_object* v___x_4200_; 
v___x_4200_ = lean_box(0);
return v___x_4200_;
}
case 1:
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_box(1);
return v___x_4201_;
}
default: 
{
lean_object* v___x_4202_; 
v___x_4202_ = lean_box(2);
return v___x_4202_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4203_){
_start:
{
uint8_t v_x_25__boxed_4204_; lean_object* v_res_4205_; 
v_x_25__boxed_4204_ = lean_unbox(v_x_4203_);
v_res_4205_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4204_);
return v_res_4205_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4206_){
_start:
{
switch(lean_obj_tag(v_x_4206_))
{
case 0:
{
uint8_t v___x_4207_; 
v___x_4207_ = 0;
return v___x_4207_;
}
case 1:
{
uint8_t v___x_4208_; 
v___x_4208_ = 1;
return v___x_4208_;
}
default: 
{
uint8_t v___x_4209_; 
v___x_4209_ = 2;
return v___x_4209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4210_){
_start:
{
uint8_t v_res_4211_; lean_object* v_r_4212_; 
v_res_4211_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4210_);
lean_dec(v_x_4210_);
v_r_4212_ = lean_box(v_res_4211_);
return v_r_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4214_, lean_object* v_numArgs_4215_){
_start:
{
switch(lean_obj_tag(v_e_4214_))
{
case 3:
{
lean_object* v_u_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v_u_4216_ = lean_ctor_get(v_e_4214_, 0);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = lean_nat_dec_eq(v_numArgs_4215_, v___x_4217_);
lean_dec(v_numArgs_4215_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_box(2);
return v___x_4219_;
}
else
{
uint8_t v___x_4220_; 
v___x_4220_ = l_Lean_Level_isNeverZero(v_u_4216_);
if (v___x_4220_ == 0)
{
uint8_t v___x_4221_; 
v___x_4221_ = l_Lean_Level_isZero(v_u_4216_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; 
v___x_4222_ = lean_box(2);
return v___x_4222_;
}
else
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_box(1);
return v___x_4223_;
}
}
else
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_box(0);
return v___x_4224_;
}
}
}
case 7:
{
lean_object* v_body_4225_; lean_object* v_zero_4226_; uint8_t v_isZero_4227_; 
v_body_4225_ = lean_ctor_get(v_e_4214_, 2);
v_zero_4226_ = lean_unsigned_to_nat(0u);
v_isZero_4227_ = lean_nat_dec_eq(v_numArgs_4215_, v_zero_4226_);
if (v_isZero_4227_ == 0)
{
lean_object* v_one_4228_; lean_object* v_n_4229_; 
v_one_4228_ = lean_unsigned_to_nat(1u);
v_n_4229_ = lean_nat_sub(v_numArgs_4215_, v_one_4228_);
lean_dec(v_numArgs_4215_);
v_e_4214_ = v_body_4225_;
v_numArgs_4215_ = v_n_4229_;
goto _start;
}
else
{
lean_object* v___x_4231_; 
lean_dec(v_numArgs_4215_);
v___x_4231_ = lean_box(2);
return v___x_4231_;
}
}
case 10:
{
lean_object* v_expr_4232_; 
v_expr_4232_ = lean_ctor_get(v_e_4214_, 1);
v_e_4214_ = v_expr_4232_;
goto _start;
}
case 5:
{
lean_object* v_fn_4234_; 
v_fn_4234_ = lean_ctor_get(v_e_4214_, 0);
if (lean_obj_tag(v_fn_4234_) == 4)
{
lean_object* v_declName_4235_; 
v_declName_4235_ = lean_ctor_get(v_fn_4234_, 0);
if (lean_obj_tag(v_declName_4235_) == 1)
{
lean_object* v_pre_4236_; 
v_pre_4236_ = lean_ctor_get(v_declName_4235_, 0);
if (lean_obj_tag(v_pre_4236_) == 0)
{
lean_object* v_arg_4237_; lean_object* v_str_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
v_arg_4237_ = lean_ctor_get(v_e_4214_, 1);
v_str_4238_ = lean_ctor_get(v_declName_4235_, 1);
v___x_4239_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4240_ = lean_string_dec_eq(v_str_4238_, v___x_4239_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; 
lean_dec(v_numArgs_4215_);
v___x_4241_ = lean_box(2);
return v___x_4241_;
}
else
{
v_e_4214_ = v_arg_4237_;
goto _start;
}
}
else
{
lean_object* v___x_4243_; 
lean_dec(v_numArgs_4215_);
v___x_4243_ = lean_box(2);
return v___x_4243_;
}
}
else
{
lean_object* v___x_4244_; 
lean_dec(v_numArgs_4215_);
v___x_4244_ = lean_box(2);
return v___x_4244_;
}
}
else
{
lean_object* v___x_4245_; 
lean_dec(v_numArgs_4215_);
v___x_4245_ = lean_box(2);
return v___x_4245_;
}
}
default: 
{
lean_object* v___x_4246_; 
lean_dec(v_numArgs_4215_);
v___x_4246_ = lean_box(2);
return v___x_4246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4247_, lean_object* v_numArgs_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4247_, v_numArgs_4248_);
lean_dec_ref(v_e_4247_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4250_, lean_object* v_binderType_4251_){
_start:
{
if (lean_obj_tag(v_r_4250_) == 3)
{
lean_object* v_idx_4252_; lean_object* v_numArgs_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4265_; 
v_idx_4252_ = lean_ctor_get(v_r_4250_, 0);
v_numArgs_4253_ = lean_ctor_get(v_r_4250_, 1);
v_isSharedCheck_4265_ = !lean_is_exclusive(v_r_4250_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4255_ = v_r_4250_;
v_isShared_4256_ = v_isSharedCheck_4265_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_numArgs_4253_);
lean_inc(v_idx_4252_);
lean_dec(v_r_4250_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4265_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v_zero_4257_; uint8_t v_isZero_4258_; 
v_zero_4257_ = lean_unsigned_to_nat(0u);
v_isZero_4258_ = lean_nat_dec_eq(v_idx_4252_, v_zero_4257_);
if (v_isZero_4258_ == 1)
{
lean_object* v___x_4259_; 
lean_del_object(v___x_4255_);
lean_dec(v_idx_4252_);
v___x_4259_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4251_, v_numArgs_4253_);
return v___x_4259_;
}
else
{
lean_object* v_one_4260_; lean_object* v_n_4261_; lean_object* v___x_4263_; 
v_one_4260_ = lean_unsigned_to_nat(1u);
v_n_4261_ = lean_nat_sub(v_idx_4252_, v_one_4260_);
lean_dec(v_idx_4252_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v_n_4261_);
v___x_4263_ = v___x_4255_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_n_4261_);
lean_ctor_set(v_reuseFailAlloc_4264_, 1, v_numArgs_4253_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
return v_r_4250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4266_, lean_object* v_binderType_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4266_, v_binderType_4267_);
lean_dec_ref(v_binderType_4267_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4269_, lean_object* v_x_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_type_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; 
switch(lean_obj_tag(v_x_4269_))
{
case 7:
{
lean_object* v_binderType_4309_; lean_object* v_body_4310_; lean_object* v_zero_4311_; uint8_t v_isZero_4312_; 
v_binderType_4309_ = lean_ctor_get(v_x_4269_, 1);
v_body_4310_ = lean_ctor_get(v_x_4269_, 2);
v_zero_4311_ = lean_unsigned_to_nat(0u);
v_isZero_4312_ = lean_nat_dec_eq(v_x_4270_, v_zero_4311_);
if (v_isZero_4312_ == 1)
{
v_type_4277_ = v_x_4269_;
v___y_4278_ = v_a_4271_;
v___y_4279_ = v_a_4272_;
v___y_4280_ = v_a_4273_;
v___y_4281_ = v_a_4274_;
goto v___jp_4276_;
}
else
{
lean_object* v_one_4313_; lean_object* v_n_4314_; lean_object* v___x_4315_; 
lean_inc_ref(v_body_4310_);
lean_inc_ref(v_binderType_4309_);
lean_dec_ref_known(v_x_4269_, 3);
v_one_4313_ = lean_unsigned_to_nat(1u);
v_n_4314_ = lean_nat_sub(v_x_4270_, v_one_4313_);
v___x_4315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4310_, v_n_4314_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_);
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
v_type_4325_ = lean_ctor_get(v_x_4269_, 1);
lean_inc_ref(v_type_4325_);
v_body_4326_ = lean_ctor_get(v_x_4269_, 3);
lean_inc_ref(v_body_4326_);
lean_dec_ref_known(v_x_4269_, 4);
v___x_4327_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4326_, v_x_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_);
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
v_expr_4337_ = lean_ctor_get(v_x_4269_, 1);
lean_inc_ref(v_expr_4337_);
lean_dec_ref_known(v_x_4269_, 2);
v_x_4269_ = v_expr_4337_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v_deBruijnIndex_4339_ = lean_ctor_get(v_x_4269_, 0);
lean_inc(v_deBruijnIndex_4339_);
lean_dec_ref_known(v_x_4269_, 1);
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = lean_nat_dec_eq(v_x_4270_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_dec(v_deBruijnIndex_4339_);
goto v___jp_4306_;
}
else
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4342_, 0, v_deBruijnIndex_4339_);
lean_ctor_set(v___x_4342_, 1, v___x_4340_);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
return v___x_4343_;
}
}
default: 
{
lean_object* v___x_4344_; uint8_t v___x_4345_; 
v___x_4344_ = lean_unsigned_to_nat(0u);
v___x_4345_ = lean_nat_dec_eq(v_x_4270_, v___x_4344_);
if (v___x_4345_ == 0)
{
lean_dec_ref(v_x_4269_);
goto v___jp_4306_;
}
else
{
v_type_4277_ = v_x_4269_;
v___y_4278_ = v_a_4271_;
v___y_4279_ = v_a_4272_;
v___y_4280_ = v_a_4273_;
v___y_4281_ = v_a_4274_;
goto v___jp_4276_;
}
}
}
v___jp_4276_:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Lean_Expr_getAppFn(v_type_4277_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_deBruijnIndex_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v_deBruijnIndex_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_deBruijnIndex_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = l_Lean_Expr_getAppNumArgs(v_type_4277_);
lean_dec_ref(v_type_4277_);
v___x_4285_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4285_, 0, v_deBruijnIndex_4283_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
return v___x_4286_;
}
else
{
lean_object* v___x_4287_; 
lean_dec_ref(v___x_4282_);
v___x_4287_ = l_Lean_Meta_isPropQuick(v_type_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
switch(lean_obj_tag(v_x_4388_))
{
case 1:
{
lean_object* v_fvarId_4394_; lean_object* v___x_4395_; 
v_fvarId_4394_ = lean_ctor_get(v_x_4388_, 0);
lean_inc(v_fvarId_4394_);
lean_dec_ref_known(v_x_4388_, 1);
v___x_4395_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4394_, v_a_4389_, v_a_4391_, v_a_4392_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v___x_4397_ = lean_unsigned_to_nat(0u);
v___x_4398_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4396_, v___x_4397_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
return v___x_4398_;
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
v_a_4399_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4395_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4395_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4407_; lean_object* v___x_4408_; 
v_mvarId_4407_ = lean_ctor_get(v_x_4388_, 0);
lean_inc(v_mvarId_4407_);
lean_dec_ref_known(v_x_4388_, 1);
v___x_4408_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4407_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v___x_4410_ = lean_unsigned_to_nat(0u);
v___x_4411_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4409_, v___x_4410_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
return v___x_4411_;
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
v_a_4412_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4408_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4408_);
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
case 3:
{
uint8_t v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
lean_dec_ref_known(v_x_4388_, 1);
v___x_4420_ = 0;
v___x_4421_ = lean_box(v___x_4420_);
v___x_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
return v___x_4422_;
}
case 4:
{
lean_object* v_declName_4423_; lean_object* v_us_4424_; lean_object* v___x_4425_; 
v_declName_4423_ = lean_ctor_get(v_x_4388_, 0);
lean_inc(v_declName_4423_);
v_us_4424_ = lean_ctor_get(v_x_4388_, 1);
lean_inc(v_us_4424_);
lean_dec_ref_known(v_x_4388_, 2);
v___x_4425_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4423_, v_us_4424_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
v___x_4427_ = lean_unsigned_to_nat(0u);
v___x_4428_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4426_, v___x_4427_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
return v___x_4428_;
}
else
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
v_a_4429_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4431_ = v___x_4425_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4425_);
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
case 5:
{
lean_object* v_fn_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_fn_4437_ = lean_ctor_get(v_x_4388_, 0);
lean_inc_ref(v_fn_4437_);
lean_dec_ref_known(v_x_4388_, 2);
v___x_4438_ = lean_unsigned_to_nat(1u);
v___x_4439_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4437_, v___x_4438_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
return v___x_4439_;
}
case 6:
{
lean_object* v_body_4440_; 
v_body_4440_ = lean_ctor_get(v_x_4388_, 2);
lean_inc_ref(v_body_4440_);
lean_dec_ref_known(v_x_4388_, 3);
v_x_4388_ = v_body_4440_;
goto _start;
}
case 7:
{
uint8_t v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
lean_dec_ref_known(v_x_4388_, 3);
v___x_4442_ = 0;
v___x_4443_ = lean_box(v___x_4442_);
v___x_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
return v___x_4444_;
}
case 8:
{
lean_object* v_body_4445_; 
v_body_4445_ = lean_ctor_get(v_x_4388_, 3);
lean_inc_ref(v_body_4445_);
lean_dec_ref_known(v_x_4388_, 4);
v_x_4388_ = v_body_4445_;
goto _start;
}
case 9:
{
uint8_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec_ref_known(v_x_4388_, 1);
v___x_4447_ = 0;
v___x_4448_ = lean_box(v___x_4447_);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
case 10:
{
lean_object* v_expr_4450_; 
v_expr_4450_ = lean_ctor_get(v_x_4388_, 1);
lean_inc_ref(v_expr_4450_);
lean_dec_ref_known(v_x_4388_, 2);
v_x_4388_ = v_expr_4450_;
goto _start;
}
default: 
{
uint8_t v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
lean_dec_ref(v_x_4388_);
v___x_4452_ = 2;
v___x_4453_ = lean_box(v___x_4452_);
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4455_, lean_object* v_x_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
switch(lean_obj_tag(v_x_4455_))
{
case 4:
{
lean_object* v_declName_4462_; lean_object* v_us_4463_; lean_object* v___x_4464_; 
v_declName_4462_ = lean_ctor_get(v_x_4455_, 0);
lean_inc(v_declName_4462_);
v_us_4463_ = lean_ctor_get(v_x_4455_, 1);
lean_inc(v_us_4463_);
lean_dec_ref_known(v_x_4455_, 2);
v___x_4464_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4462_, v_us_4463_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v_a_4465_; lean_object* v___x_4466_; 
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4465_);
lean_dec_ref_known(v___x_4464_, 1);
v___x_4466_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4465_, v_x_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_x_4456_);
return v___x_4466_;
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec(v_x_4456_);
v_a_4467_ = lean_ctor_get(v___x_4464_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4464_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4464_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4475_; lean_object* v___x_4476_; 
v_fvarId_4475_ = lean_ctor_get(v_x_4455_, 0);
lean_inc(v_fvarId_4475_);
lean_dec_ref_known(v_x_4455_, 1);
v___x_4476_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4475_, v_a_4457_, v_a_4459_, v_a_4460_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4478_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
v___x_4478_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4477_, v_x_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_x_4456_);
return v___x_4478_;
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
lean_dec(v_x_4456_);
v_a_4479_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4481_ = v___x_4476_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4476_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4487_; lean_object* v___x_4488_; 
v_mvarId_4487_ = lean_ctor_get(v_x_4455_, 0);
lean_inc(v_mvarId_4487_);
lean_dec_ref_known(v_x_4455_, 1);
v___x_4488_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4487_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4490_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v___x_4490_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4489_, v_x_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_x_4456_);
return v___x_4490_;
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
lean_dec(v_x_4456_);
v_a_4491_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4493_ = v___x_4488_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v___x_4488_);
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
v_fn_4499_ = lean_ctor_get(v_x_4455_, 0);
lean_inc_ref(v_fn_4499_);
lean_dec_ref_known(v_x_4455_, 2);
v___x_4500_ = lean_unsigned_to_nat(1u);
v___x_4501_ = lean_nat_add(v_x_4456_, v___x_4500_);
lean_dec(v_x_4456_);
v_x_4455_ = v_fn_4499_;
v_x_4456_ = v___x_4501_;
goto _start;
}
case 10:
{
lean_object* v_expr_4503_; 
v_expr_4503_ = lean_ctor_get(v_x_4455_, 1);
lean_inc_ref(v_expr_4503_);
lean_dec_ref_known(v_x_4455_, 2);
v_x_4455_ = v_expr_4503_;
goto _start;
}
case 8:
{
lean_object* v_body_4505_; 
v_body_4505_ = lean_ctor_get(v_x_4455_, 3);
lean_inc_ref(v_body_4505_);
lean_dec_ref_known(v_x_4455_, 4);
v_x_4455_ = v_body_4505_;
goto _start;
}
case 6:
{
lean_object* v_body_4507_; lean_object* v_zero_4508_; uint8_t v_isZero_4509_; 
v_body_4507_ = lean_ctor_get(v_x_4455_, 2);
lean_inc_ref(v_body_4507_);
lean_dec_ref_known(v_x_4455_, 3);
v_zero_4508_ = lean_unsigned_to_nat(0u);
v_isZero_4509_ = lean_nat_dec_eq(v_x_4456_, v_zero_4508_);
if (v_isZero_4509_ == 1)
{
lean_object* v___x_4510_; 
lean_dec(v_x_4456_);
v___x_4510_ = l_Lean_Meta_isProofQuick(v_body_4507_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
return v___x_4510_;
}
else
{
lean_object* v_one_4511_; lean_object* v_n_4512_; 
v_one_4511_ = lean_unsigned_to_nat(1u);
v_n_4512_ = lean_nat_sub(v_x_4456_, v_one_4511_);
lean_dec(v_x_4456_);
v_x_4455_ = v_body_4507_;
v_x_4456_ = v_n_4512_;
goto _start;
}
}
default: 
{
uint8_t v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
lean_dec(v_x_4456_);
lean_dec_ref(v_x_4455_);
v___x_4514_ = 2;
v___x_4515_ = lean_box(v___x_4514_);
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4517_, lean_object* v_x_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4517_, v_x_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_Meta_isProofQuick(v_x_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v___x_4538_; 
lean_inc_ref(v_e_4532_);
v___x_4538_ = l_Lean_Meta_isProofQuick(v_e_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4565_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4541_ = v___x_4538_;
v_isShared_4542_ = v_isSharedCheck_4565_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4538_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4565_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
uint8_t v___x_4543_; 
v___x_4543_ = lean_unbox(v_a_4539_);
lean_dec(v_a_4539_);
switch(v___x_4543_)
{
case 0:
{
uint8_t v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4547_; 
lean_dec_ref(v_e_4532_);
v___x_4544_ = 0;
v___x_4545_ = lean_box(v___x_4544_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4545_);
v___x_4547_ = v___x_4541_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
case 1:
{
uint8_t v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4552_; 
lean_dec_ref(v_e_4532_);
v___x_4549_ = 1;
v___x_4550_ = lean_box(v___x_4549_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4550_);
v___x_4552_ = v___x_4541_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4550_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
default: 
{
lean_object* v___x_4554_; 
lean_del_object(v___x_4541_);
lean_inc(v_a_4536_);
lean_inc_ref(v_a_4535_);
lean_inc(v_a_4534_);
lean_inc_ref(v_a_4533_);
v___x_4554_ = lean_infer_type(v_e_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; lean_object* v___x_4556_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v___x_4554_, 1);
v___x_4556_ = l_Lean_Meta_isProp(v_a_4555_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_);
return v___x_4556_;
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
v_a_4557_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4554_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4554_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec_ref(v_e_4532_);
v_a_4566_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4538_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4538_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Meta_isProof(v_e_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4581_, lean_object* v_x_4582_){
_start:
{
switch(lean_obj_tag(v_x_4581_))
{
case 3:
{
lean_object* v___x_4588_; uint8_t v___x_4589_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v___x_4589_ = lean_nat_dec_eq(v_x_4582_, v___x_4588_);
lean_dec(v_x_4582_);
if (v___x_4589_ == 0)
{
goto v___jp_4584_;
}
else
{
uint8_t v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4590_ = 1;
v___x_4591_ = lean_box(v___x_4590_);
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
return v___x_4592_;
}
}
case 7:
{
lean_object* v_body_4593_; lean_object* v_zero_4594_; uint8_t v_isZero_4595_; 
v_body_4593_ = lean_ctor_get(v_x_4581_, 2);
v_zero_4594_ = lean_unsigned_to_nat(0u);
v_isZero_4595_ = lean_nat_dec_eq(v_x_4582_, v_zero_4594_);
if (v_isZero_4595_ == 1)
{
uint8_t v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
lean_dec(v_x_4582_);
v___x_4596_ = 0;
v___x_4597_ = lean_box(v___x_4596_);
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4597_);
return v___x_4598_;
}
else
{
lean_object* v_one_4599_; lean_object* v_n_4600_; 
v_one_4599_ = lean_unsigned_to_nat(1u);
v_n_4600_ = lean_nat_sub(v_x_4582_, v_one_4599_);
lean_dec(v_x_4582_);
v_x_4581_ = v_body_4593_;
v_x_4582_ = v_n_4600_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4602_; 
v_body_4602_ = lean_ctor_get(v_x_4581_, 3);
v_x_4581_ = v_body_4602_;
goto _start;
}
case 10:
{
lean_object* v_expr_4604_; 
v_expr_4604_ = lean_ctor_get(v_x_4581_, 1);
v_x_4581_ = v_expr_4604_;
goto _start;
}
default: 
{
lean_dec(v_x_4582_);
goto v___jp_4584_;
}
}
v___jp_4584_:
{
uint8_t v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4585_ = 2;
v___x_4586_ = lean_box(v___x_4585_);
v___x_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
return v___x_4587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4606_, lean_object* v_x_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4606_, v_x_4607_);
lean_dec_ref(v_x_4606_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4610_, lean_object* v_x_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4610_, v_x_4611_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4618_, lean_object* v_x_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4618_, v_x_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec_ref(v_x_4618_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4626_, lean_object* v_x_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
switch(lean_obj_tag(v_x_4626_))
{
case 4:
{
lean_object* v_declName_4633_; lean_object* v_us_4634_; lean_object* v___x_4635_; 
v_declName_4633_ = lean_ctor_get(v_x_4626_, 0);
lean_inc(v_declName_4633_);
v_us_4634_ = lean_ctor_get(v_x_4626_, 1);
lean_inc(v_us_4634_);
lean_dec_ref_known(v_x_4626_, 2);
v___x_4635_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4633_, v_us_4634_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v___x_4637_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
lean_dec_ref_known(v___x_4635_, 1);
v___x_4637_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4636_, v_x_4627_);
lean_dec(v_a_4636_);
return v___x_4637_;
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
lean_dec(v_x_4627_);
v_a_4638_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4635_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4635_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4646_; lean_object* v___x_4647_; 
v_fvarId_4646_ = lean_ctor_get(v_x_4626_, 0);
lean_inc(v_fvarId_4646_);
lean_dec_ref_known(v_x_4626_, 1);
v___x_4647_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4646_, v_a_4628_, v_a_4630_, v_a_4631_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4649_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
lean_dec_ref_known(v___x_4647_, 1);
v___x_4649_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4648_, v_x_4627_);
lean_dec(v_a_4648_);
return v___x_4649_;
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_dec(v_x_4627_);
v_a_4650_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4647_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4647_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4658_; lean_object* v___x_4659_; 
v_mvarId_4658_ = lean_ctor_get(v_x_4626_, 0);
lean_inc(v_mvarId_4658_);
lean_dec_ref_known(v_x_4626_, 1);
v___x_4659_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4658_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4661_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4660_);
lean_dec_ref_known(v___x_4659_, 1);
v___x_4661_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4660_, v_x_4627_);
lean_dec(v_a_4660_);
return v___x_4661_;
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec(v_x_4627_);
v_a_4662_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4659_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4659_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
case 5:
{
lean_object* v_fn_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v_fn_4670_ = lean_ctor_get(v_x_4626_, 0);
lean_inc_ref(v_fn_4670_);
lean_dec_ref_known(v_x_4626_, 2);
v___x_4671_ = lean_unsigned_to_nat(1u);
v___x_4672_ = lean_nat_add(v_x_4627_, v___x_4671_);
lean_dec(v_x_4627_);
v_x_4626_ = v_fn_4670_;
v_x_4627_ = v___x_4672_;
goto _start;
}
case 10:
{
lean_object* v_expr_4674_; 
v_expr_4674_ = lean_ctor_get(v_x_4626_, 1);
lean_inc_ref(v_expr_4674_);
lean_dec_ref_known(v_x_4626_, 2);
v_x_4626_ = v_expr_4674_;
goto _start;
}
case 8:
{
lean_object* v_body_4676_; 
v_body_4676_ = lean_ctor_get(v_x_4626_, 3);
lean_inc_ref(v_body_4676_);
lean_dec_ref_known(v_x_4626_, 4);
v_x_4626_ = v_body_4676_;
goto _start;
}
case 6:
{
lean_object* v_body_4678_; lean_object* v_zero_4679_; uint8_t v_isZero_4680_; 
v_body_4678_ = lean_ctor_get(v_x_4626_, 2);
lean_inc_ref(v_body_4678_);
lean_dec_ref_known(v_x_4626_, 3);
v_zero_4679_ = lean_unsigned_to_nat(0u);
v_isZero_4680_ = lean_nat_dec_eq(v_x_4627_, v_zero_4679_);
if (v_isZero_4680_ == 1)
{
uint8_t v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
lean_dec_ref(v_body_4678_);
lean_dec(v_x_4627_);
v___x_4681_ = 0;
v___x_4682_ = lean_box(v___x_4681_);
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
return v___x_4683_;
}
else
{
lean_object* v_one_4684_; lean_object* v_n_4685_; 
v_one_4684_ = lean_unsigned_to_nat(1u);
v_n_4685_ = lean_nat_sub(v_x_4627_, v_one_4684_);
lean_dec(v_x_4627_);
v_x_4626_ = v_body_4678_;
v_x_4627_ = v_n_4685_;
goto _start;
}
}
default: 
{
uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
lean_dec(v_x_4627_);
lean_dec_ref(v_x_4626_);
v___x_4687_ = 2;
v___x_4688_ = lean_box(v___x_4687_);
v___x_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
return v___x_4689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4690_, lean_object* v_x_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4690_, v_x_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
switch(lean_obj_tag(v_x_4698_))
{
case 1:
{
lean_object* v_fvarId_4704_; lean_object* v___x_4705_; 
v_fvarId_4704_ = lean_ctor_get(v_x_4698_, 0);
lean_inc(v_fvarId_4704_);
lean_dec_ref_known(v_x_4698_, 1);
v___x_4705_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4704_, v_a_4699_, v_a_4701_, v_a_4702_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_a_4706_);
lean_dec_ref_known(v___x_4705_, 1);
v___x_4707_ = lean_unsigned_to_nat(0u);
v___x_4708_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4706_, v___x_4707_);
lean_dec(v_a_4706_);
return v___x_4708_;
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
v_a_4709_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4705_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4705_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4717_; lean_object* v___x_4718_; 
v_mvarId_4717_ = lean_ctor_get(v_x_4698_, 0);
lean_inc(v_mvarId_4717_);
lean_dec_ref_known(v_x_4698_, 1);
v___x_4718_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4717_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4718_, 1);
v___x_4720_ = lean_unsigned_to_nat(0u);
v___x_4721_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4719_, v___x_4720_);
lean_dec(v_a_4719_);
return v___x_4721_;
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
v_a_4722_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4718_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4718_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
case 3:
{
uint8_t v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
lean_dec_ref_known(v_x_4698_, 1);
v___x_4730_ = 1;
v___x_4731_ = lean_box(v___x_4730_);
v___x_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4731_);
return v___x_4732_;
}
case 4:
{
lean_object* v_declName_4733_; lean_object* v_us_4734_; lean_object* v___x_4735_; 
v_declName_4733_ = lean_ctor_get(v_x_4698_, 0);
lean_inc(v_declName_4733_);
v_us_4734_ = lean_ctor_get(v_x_4698_, 1);
lean_inc(v_us_4734_);
lean_dec_ref_known(v_x_4698_, 2);
v___x_4735_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4733_, v_us_4734_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
v___x_4737_ = lean_unsigned_to_nat(0u);
v___x_4738_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4736_, v___x_4737_);
lean_dec(v_a_4736_);
return v___x_4738_;
}
else
{
lean_object* v_a_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4746_; 
v_a_4739_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4741_ = v___x_4735_;
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_a_4739_);
lean_dec(v___x_4735_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
if (v_isShared_4742_ == 0)
{
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4739_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
case 5:
{
lean_object* v_fn_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; 
v_fn_4747_ = lean_ctor_get(v_x_4698_, 0);
lean_inc_ref(v_fn_4747_);
lean_dec_ref_known(v_x_4698_, 2);
v___x_4748_ = lean_unsigned_to_nat(1u);
v___x_4749_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4747_, v___x_4748_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
return v___x_4749_;
}
case 6:
{
uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
lean_dec_ref_known(v_x_4698_, 3);
v___x_4750_ = 0;
v___x_4751_ = lean_box(v___x_4750_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
return v___x_4752_;
}
case 7:
{
uint8_t v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
lean_dec_ref_known(v_x_4698_, 3);
v___x_4753_ = 1;
v___x_4754_ = lean_box(v___x_4753_);
v___x_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
return v___x_4755_;
}
case 8:
{
lean_object* v_body_4756_; 
v_body_4756_ = lean_ctor_get(v_x_4698_, 3);
lean_inc_ref(v_body_4756_);
lean_dec_ref_known(v_x_4698_, 4);
v_x_4698_ = v_body_4756_;
goto _start;
}
case 9:
{
uint8_t v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
lean_dec_ref_known(v_x_4698_, 1);
v___x_4758_ = 0;
v___x_4759_ = lean_box(v___x_4758_);
v___x_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
return v___x_4760_;
}
case 10:
{
lean_object* v_expr_4761_; 
v_expr_4761_ = lean_ctor_get(v_x_4698_, 1);
lean_inc_ref(v_expr_4761_);
lean_dec_ref_known(v_x_4698_, 2);
v_x_4698_ = v_expr_4761_;
goto _start;
}
default: 
{
uint8_t v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
lean_dec_ref(v_x_4698_);
v___x_4763_ = 2;
v___x_4764_ = lean_box(v___x_4763_);
v___x_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4764_);
return v___x_4765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_Meta_isTypeQuick(v_x_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___x_4779_; 
lean_inc_ref(v_e_4773_);
v___x_4779_ = l_Lean_Meta_isTypeQuick(v_e_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4829_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4782_ = v___x_4779_;
v_isShared_4783_ = v_isSharedCheck_4829_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4829_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
uint8_t v___x_4784_; 
v___x_4784_ = lean_unbox(v_a_4780_);
lean_dec(v_a_4780_);
switch(v___x_4784_)
{
case 0:
{
uint8_t v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4788_; 
lean_dec_ref(v_e_4773_);
v___x_4785_ = 0;
v___x_4786_ = lean_box(v___x_4785_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4786_);
v___x_4788_ = v___x_4782_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
case 1:
{
uint8_t v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4793_; 
lean_dec_ref(v_e_4773_);
v___x_4790_ = 1;
v___x_4791_ = lean_box(v___x_4790_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4791_);
v___x_4793_ = v___x_4782_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4791_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
default: 
{
lean_object* v___x_4795_; 
lean_del_object(v___x_4782_);
lean_inc(v_a_4777_);
lean_inc_ref(v_a_4776_);
lean_inc(v_a_4775_);
lean_inc_ref(v_a_4774_);
v___x_4795_ = lean_infer_type(v_e_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4797_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref_known(v___x_4795_, 1);
v___x_4797_ = l_Lean_Meta_whnfD(v_a_4796_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4812_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4800_ = v___x_4797_;
v_isShared_4801_ = v_isSharedCheck_4812_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4797_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4812_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
if (lean_obj_tag(v_a_4798_) == 3)
{
uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4805_; 
lean_dec_ref_known(v_a_4798_, 1);
v___x_4802_ = 1;
v___x_4803_ = lean_box(v___x_4802_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4803_);
v___x_4805_ = v___x_4800_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
else
{
uint8_t v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4810_; 
lean_dec(v_a_4798_);
v___x_4807_ = 0;
v___x_4808_ = lean_box(v___x_4807_);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 0, v___x_4808_);
v___x_4810_ = v___x_4800_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v___x_4808_);
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
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
v_a_4813_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4797_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4797_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
v_a_4821_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4795_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4795_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec_ref(v_e_4773_);
v_a_4830_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4779_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4779_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_Meta_isType(v_e_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4845_){
_start:
{
switch(lean_obj_tag(v_x_4845_))
{
case 7:
{
lean_object* v_body_4846_; 
v_body_4846_ = lean_ctor_get(v_x_4845_, 2);
v_x_4845_ = v_body_4846_;
goto _start;
}
case 3:
{
lean_object* v_u_4848_; lean_object* v___x_4849_; 
v_u_4848_ = lean_ctor_get(v_x_4845_, 0);
lean_inc(v_u_4848_);
v___x_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4849_, 0, v_u_4848_);
return v___x_4849_;
}
default: 
{
lean_object* v___x_4850_; 
v___x_4850_ = lean_box(0);
return v___x_4850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4851_);
lean_dec_ref(v_x_4851_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4853_, lean_object* v_body_4854_, lean_object* v_x_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4853_, v_body_4854_, v_x_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4864_, lean_object* v_xs_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v_l_4872_; 
switch(lean_obj_tag(v_type_4864_))
{
case 3:
{
lean_object* v_u_4875_; 
lean_dec_ref(v_xs_4865_);
v_u_4875_ = lean_ctor_get(v_type_4864_, 0);
lean_inc(v_u_4875_);
lean_dec_ref_known(v_type_4864_, 1);
v_l_4872_ = v_u_4875_;
goto v___jp_4871_;
}
case 7:
{
lean_object* v_binderName_4876_; lean_object* v_binderType_4877_; lean_object* v_body_4878_; uint8_t v_binderInfo_4879_; lean_object* v___f_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v_binderName_4876_ = lean_ctor_get(v_type_4864_, 0);
lean_inc(v_binderName_4876_);
v_binderType_4877_ = lean_ctor_get(v_type_4864_, 1);
lean_inc_ref(v_binderType_4877_);
v_body_4878_ = lean_ctor_get(v_type_4864_, 2);
lean_inc_ref(v_body_4878_);
v_binderInfo_4879_ = lean_ctor_get_uint8(v_type_4864_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4864_, 3);
lean_inc_ref(v_xs_4865_);
v___f_4880_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4880_, 0, v_xs_4865_);
lean_closure_set(v___f_4880_, 1, v_body_4878_);
v___x_4881_ = lean_expr_instantiate_rev(v_binderType_4877_, v_xs_4865_);
lean_dec_ref(v_xs_4865_);
lean_dec_ref(v_binderType_4877_);
v___x_4882_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4876_, v_binderInfo_4879_, v___x_4881_, v___f_4880_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_);
return v___x_4882_;
}
default: 
{
lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4883_ = lean_expr_instantiate_rev(v_type_4864_, v_xs_4865_);
lean_dec_ref(v_xs_4865_);
lean_dec_ref(v_type_4864_);
v___x_4884_ = l_Lean_Meta_whnfD(v___x_4883_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4896_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4887_ = v___x_4884_;
v_isShared_4888_ = v_isSharedCheck_4896_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4884_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4896_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
switch(lean_obj_tag(v_a_4885_))
{
case 3:
{
lean_object* v_u_4889_; 
lean_del_object(v___x_4887_);
v_u_4889_ = lean_ctor_get(v_a_4885_, 0);
lean_inc(v_u_4889_);
lean_dec_ref_known(v_a_4885_, 1);
v_l_4872_ = v_u_4889_;
goto v___jp_4871_;
}
case 7:
{
lean_object* v___x_4890_; 
lean_del_object(v___x_4887_);
v___x_4890_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4864_ = v_a_4885_;
v_xs_4865_ = v___x_4890_;
goto _start;
}
default: 
{
lean_object* v___x_4892_; lean_object* v___x_4894_; 
lean_dec(v_a_4885_);
v___x_4892_ = lean_box(0);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v___x_4892_);
v___x_4894_ = v___x_4887_;
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
v_a_4897_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4884_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4884_);
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
v___jp_4871_:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4873_, 0, v_l_4872_);
v___x_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
return v___x_4874_;
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
lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4935_ = lean_box(0);
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 1, v_cache_4924_);
v___x_4937_ = v___x_4933_;
goto v_reusejp_4936_;
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
v___x_4937_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4938_ = lean_st_ref_put(v_a_4923_, v___x_4937_);
v___x_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4935_);
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
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v_cache_4957_; lean_object* v___x_4958_; 
v___x_4955_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4956_ = lean_st_ref_get(v_a_4950_);
v_cache_4957_ = lean_ctor_get(v___x_4956_, 1);
lean_inc_ref(v_cache_4957_);
lean_dec(v___x_4956_);
v___x_4958_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4948_, v___x_4955_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
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
v___x_4965_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4950_, v_cache_4957_, v___x_4964_);
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
v___x_4978_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4950_, v_cache_4957_, v___x_4977_);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5032_, lean_object* v_x_5033_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5040_, lean_object* v_x_5041_){
_start:
{
uint8_t v_res_5042_; lean_object* v_r_5043_; 
v_res_5042_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5040_, v_x_5041_);
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
v___x_5058_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5053_, v___x_5057_);
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
size_t v___x_5194_; size_t v___x_5195_; uint8_t v___x_5196_; 
v___x_5194_ = ((size_t)0ULL);
v___x_5195_ = lean_usize_of_nat(v___x_5192_);
v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5190_, v_as_5189_, v___x_5194_, v___x_5195_);
return v___x_5196_;
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
lean_object* v_v_5294_; lean_object* v___x_5295_; lean_object* v_bs_x27_5296_; lean_object* v___x_5297_; 
v_v_5294_ = lean_array_uget(v_bs_5286_, v_i_5285_);
v___x_5295_ = lean_unsigned_to_nat(0u);
v_bs_x27_5296_ = lean_array_uset(v_bs_5286_, v_i_5285_, v___x_5295_);
lean_inc(v___y_5290_);
lean_inc_ref(v___y_5289_);
lean_inc(v___y_5288_);
lean_inc_ref(v___y_5287_);
v___x_5297_ = lean_infer_type(v_v_5294_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v_a_5298_; size_t v___x_5299_; size_t v___x_5300_; lean_object* v___x_5301_; 
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
lean_inc(v_a_5298_);
lean_dec_ref_known(v___x_5297_, 1);
v___x_5299_ = ((size_t)1ULL);
v___x_5300_ = lean_usize_add(v_i_5285_, v___x_5299_);
v___x_5301_ = lean_array_uset(v_bs_x27_5296_, v_i_5285_, v_a_5298_);
v_i_5285_ = v___x_5300_;
v_bs_5286_ = v___x_5301_;
goto _start;
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
lean_dec_ref(v_bs_x27_5296_);
v_a_5303_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___x_5297_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5297_);
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
