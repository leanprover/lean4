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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
lean_dec_ref_known(v_e_285_, 2);
lean_dec_ref(v_fn_290_);
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
v___x_314_ = lean_unsigned_to_nat(1864u);
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
lean_object* v___x_684_; lean_object* v_env_685_; uint8_t v___x_686_; lean_object* v_env_687_; lean_object* v___x_688_; lean_object* v_toCold_689_; lean_object* v_mctx_690_; lean_object* v_lctx_691_; lean_object* v_options_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_684_ = lean_st_ref_get(v___y_682_);
v_env_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_env_685_);
lean_dec(v___x_684_);
v___x_686_ = 0;
v_env_687_ = l_Lean_Environment_setRecordingDeps(v_env_685_, v___x_686_);
v___x_688_ = lean_st_ref_get(v___y_680_);
v_toCold_689_ = lean_ctor_get(v___y_681_, 0);
v_mctx_690_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_mctx_690_);
lean_dec(v___x_688_);
v_lctx_691_ = lean_ctor_get(v___y_679_, 2);
v_options_692_ = lean_ctor_get(v_toCold_689_, 2);
lean_inc_ref(v_options_692_);
lean_inc_ref(v_lctx_691_);
v___x_693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_693_, 0, v_env_687_);
lean_ctor_set(v___x_693_, 1, v_mctx_690_);
lean_ctor_set(v___x_693_, 2, v_lctx_691_);
lean_ctor_set(v___x_693_, 3, v_options_692_);
v___x_694_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_msgData_678_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_ref_709_; lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
v_ref_709_ = lean_ctor_get(v___y_706_, 2);
v___x_710_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_719_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_inc(v_ref_709_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_ref_709_);
lean_ctor_set(v___x_715_, 1, v_a_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 1);
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
return v_res_726_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_729_ = l_Lean_stringToMessageData(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_737_ = l_Lean_indentExpr(v_f_730_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_738_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_747_, lean_object* v_f_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_755_, lean_object* v_f_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_755_, v_f_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_763_, lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_771_, lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_771_, v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_779_, lean_object* v_args_780_, lean_object* v_f_781_, lean_object* v_a_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_a_790_; uint8_t v___x_794_; 
v___x_794_ = lean_nat_dec_lt(v_a_782_, v_upperBound_779_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v_a_782_);
lean_dec_ref(v_f_781_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v_b_783_);
return v___x_795_;
}
else
{
lean_object* v_fst_796_; 
v_fst_796_ = lean_ctor_get(v_b_783_, 0);
lean_inc(v_fst_796_);
if (lean_obj_tag(v_fst_796_) == 7)
{
lean_object* v_snd_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_snd_797_ = lean_ctor_get(v_b_783_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_b_783_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v_b_783_, 0);
lean_dec(v_unused_806_);
v___x_799_ = v_b_783_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_snd_797_);
lean_dec(v_b_783_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_body_801_; lean_object* v___x_803_; 
v_body_801_ = lean_ctor_get(v_fst_796_, 2);
lean_inc_ref(v_body_801_);
lean_dec_ref_known(v_fst_796_, 3);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_body_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_body_801_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_snd_797_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v_a_790_ = v___x_803_;
goto v___jp_789_;
}
}
}
else
{
lean_object* v_snd_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_842_; 
v_snd_807_ = lean_ctor_get(v_b_783_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_b_783_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_b_783_, 0);
lean_dec(v_unused_843_);
v___x_809_ = v_b_783_;
v_isShared_810_ = v_isSharedCheck_842_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snd_807_);
lean_dec(v_b_783_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_842_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_782_);
lean_inc(v_fst_796_);
v___x_812_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_796_, v_snd_807_, v_a_782_, v_args_780_);
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
v___x_813_ = lean_whnf(v___x_812_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
if (lean_obj_tag(v_a_814_) == 7)
{
lean_object* v_body_815_; lean_object* v___x_817_; 
lean_dec(v_snd_807_);
lean_dec(v_fst_796_);
v_body_815_ = lean_ctor_get(v_a_814_, 2);
lean_inc_ref(v_body_815_);
lean_dec_ref_known(v_a_814_, 3);
lean_inc(v_a_782_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v_a_782_);
lean_ctor_set(v___x_809_, 0, v_body_815_);
v___x_817_ = v___x_809_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_body_815_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_a_782_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v_a_790_ = v___x_817_;
goto v___jp_789_;
}
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_a_814_);
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_add(v_a_782_, v___x_819_);
lean_inc_ref(v_f_781_);
v___x_821_ = l_Lean_mkAppRange(v_f_781_, v___x_811_, v___x_820_, v_args_780_);
lean_dec(v___x_820_);
v___x_822_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_821_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_824_; 
lean_dec_ref_known(v___x_822_, 1);
if (v_isShared_810_ == 0)
{
v___x_824_ = v___x_809_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_fst_796_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_snd_807_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v_a_790_ = v___x_824_;
goto v___jp_789_;
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_del_object(v___x_809_);
lean_dec(v_snd_807_);
lean_dec(v_fst_796_);
lean_dec(v_a_782_);
lean_dec_ref(v_f_781_);
v_a_826_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_822_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_822_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_del_object(v___x_809_);
lean_dec(v_snd_807_);
lean_dec(v_fst_796_);
lean_dec(v_a_782_);
lean_dec_ref(v_f_781_);
v_a_834_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_813_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_813_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
v___jp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_add(v_a_782_, v___x_791_);
lean_dec(v_a_782_);
v_a_782_ = v___x_792_;
v_b_783_ = v_a_790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_844_, lean_object* v_args_845_, lean_object* v_f_846_, lean_object* v_a_847_, lean_object* v_b_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_844_, v_args_845_, v_f_846_, v_a_847_, v_b_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec_ref(v_args_845_);
lean_dec(v_upperBound_844_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_855_, lean_object* v_args_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
lean_inc(v_a_860_);
lean_inc_ref(v_a_859_);
lean_inc(v_a_858_);
lean_inc_ref(v_a_857_);
lean_inc_ref(v_f_855_);
v___x_862_ = lean_infer_type(v_f_855_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_array_get_size(v_args_856_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_a_863_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_864_, v_args_856_, v_f_855_, v___x_865_, v___x_866_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_878_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_878_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_878_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v_fst_872_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_fst_872_);
v_snd_873_ = lean_ctor_get(v_a_868_, 1);
lean_inc(v_snd_873_);
lean_dec(v_a_868_);
v___x_874_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_872_, v_snd_873_, v___x_864_, v_args_856_);
lean_dec(v_snd_873_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_874_);
v___x_876_ = v___x_870_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_867_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_867_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_dec_ref(v_f_855_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_887_, lean_object* v_args_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_887_, v_args_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec_ref(v_args_888_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_895_, lean_object* v_args_896_, lean_object* v_f_897_, lean_object* v_inst_898_, lean_object* v_R_899_, lean_object* v_a_900_, lean_object* v_b_901_, lean_object* v_c_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_895_, v_args_896_, v_f_897_, v_a_900_, v_b_901_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_909_, lean_object* v_args_910_, lean_object* v_f_911_, lean_object* v_inst_912_, lean_object* v_R_913_, lean_object* v_a_914_, lean_object* v_b_915_, lean_object* v_c_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_909_, v_args_910_, v_f_911_, v_inst_912_, v_R_913_, v_a_914_, v_b_915_, v_c_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_args_910_);
lean_dec(v_upperBound_909_);
return v_res_922_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_925_ = l_Lean_stringToMessageData(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_926_, lean_object* v_us_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_933_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_934_ = l_Lean_mkConst(v_constName_926_, v_us_927_);
v___x_935_ = l_Lean_MessageData_ofExpr(v___x_934_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_933_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_936_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_938_, lean_object* v_us_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_938_, v_us_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_946_, lean_object* v_constName_947_, lean_object* v_us_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_947_, v_us_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_955_, lean_object* v_constName_956_, lean_object* v_us_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_955_, v_constName_956_, v_us_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_964_, lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_toCold_971_; lean_object* v_currRecDepth_972_; lean_object* v_ref_973_; uint16_t v_optionFlags_974_; uint8_t v_suppressElabErrors_975_; uint8_t v_isRecordingDeps_976_; lean_object* v_ref_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_toCold_971_ = lean_ctor_get(v___y_968_, 0);
v_currRecDepth_972_ = lean_ctor_get(v___y_968_, 1);
v_ref_973_ = lean_ctor_get(v___y_968_, 2);
v_optionFlags_974_ = lean_ctor_get_uint16(v___y_968_, sizeof(void*)*3);
v_suppressElabErrors_975_ = lean_ctor_get_uint8(v___y_968_, sizeof(void*)*3 + 2);
v_isRecordingDeps_976_ = lean_ctor_get_uint8(v___y_968_, sizeof(void*)*3 + 3);
v_ref_977_ = l_Lean_replaceRef(v_ref_964_, v_ref_973_);
lean_inc(v_currRecDepth_972_);
lean_inc_ref(v_toCold_971_);
v___x_978_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_978_, 0, v_toCold_971_);
lean_ctor_set(v___x_978_, 1, v_currRecDepth_972_);
lean_ctor_set(v___x_978_, 2, v_ref_977_);
lean_ctor_set_uint16(v___x_978_, sizeof(void*)*3, v_optionFlags_974_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*3 + 2, v_suppressElabErrors_975_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*3 + 3, v_isRecordingDeps_976_);
v___x_979_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_965_, v___y_966_, v___y_967_, v___x_978_, v___y_969_);
lean_dec_ref_known(v___x_978_, 3);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_980_, lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_980_, v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v_ref_980_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_988_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_991_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
lean_ctor_set(v___x_994_, 2, v___x_993_);
lean_ctor_set(v___x_994_, 3, v___x_993_);
lean_ctor_set(v___x_994_, 4, v___x_992_);
lean_ctor_set(v___x_994_, 5, v___x_992_);
lean_ctor_set(v___x_994_, 6, v___x_992_);
lean_ctor_set(v___x_994_, 7, v___x_992_);
lean_ctor_set(v___x_994_, 8, v___x_992_);
lean_ctor_set(v___x_994_, 9, v___x_992_);
lean_ctor_set(v___x_994_, 10, v___x_992_);
lean_ctor_set(v___x_994_, 11, v___x_991_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_unsigned_to_nat(32u);
v___x_996_ = lean_mk_empty_array_with_capacity(v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_998_ = ((size_t)5ULL);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_unsigned_to_nat(32u);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1003_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_1001_);
lean_ctor_set(v___x_1003_, 2, v___x_999_);
lean_ctor_set(v___x_1003_, 3, v___x_999_);
lean_ctor_set_usize(v___x_1003_, 4, v___x_998_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1004_ = lean_box(1);
v___x_1005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
lean_ctor_set(v___x_1007_, 2, v___x_1004_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1041_, lean_object* v_declHint_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_env_1047_; uint8_t v___x_1048_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_st_ref_get(v___y_1043_);
v_env_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc_ref(v_env_1047_);
lean_dec(v___x_1046_);
v___x_1048_ = l_Lean_Name_isAnonymous(v_declHint_1042_);
if (v___x_1048_ == 0)
{
uint8_t v_isExporting_1049_; 
v_isExporting_1049_ = lean_ctor_get_uint8(v_env_1047_, sizeof(void*)*13);
if (v_isExporting_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1042_);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v_msg_1041_);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
lean_inc_ref(v_env_1047_);
v___x_1051_ = l_Lean_Environment_setExporting(v_env_1047_, v___x_1048_);
lean_inc(v_declHint_1042_);
lean_inc_ref(v___x_1051_);
v___x_1052_ = l_Lean_Environment_contains(v___x_1051_, v_declHint_1042_, v_isExporting_1049_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v___x_1051_);
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1042_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_msg_1041_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_c_1059_; lean_object* v___x_1060_; 
v___x_1054_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1055_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1056_ = l_Lean_Options_empty;
v___x_1057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1051_);
lean_ctor_set(v___x_1057_, 1, v___x_1054_);
lean_ctor_set(v___x_1057_, 2, v___x_1055_);
lean_ctor_set(v___x_1057_, 3, v___x_1056_);
lean_inc(v_declHint_1042_);
v___x_1058_ = l_Lean_MessageData_ofConstName(v_declHint_1042_, v___x_1048_);
v_c_1059_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1059_, 0, v___x_1057_);
lean_ctor_set(v_c_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1047_, v_declHint_1042_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1042_);
v___x_1061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_c_1059_);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_MessageData_note(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_msg_1041_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1124_; 
v_val_1068_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1070_ = v___x_1060_;
v_isShared_1071_ = v_isSharedCheck_1124_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_val_1068_);
lean_dec(v___x_1060_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1124_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v_modules_1073_; lean_object* v_moduleNames_1074_; lean_object* v_mod_1075_; uint8_t v___y_1077_; uint8_t v___x_1107_; 
v___x_1072_ = l_Lean_Environment_header(v_env_1047_);
lean_dec_ref(v_env_1047_);
v_modules_1073_ = lean_ctor_get(v___x_1072_, 3);
lean_inc_ref(v_modules_1073_);
v_moduleNames_1074_ = lean_ctor_get(v___x_1072_, 4);
lean_inc_ref(v_moduleNames_1074_);
lean_dec_ref(v___x_1072_);
v_mod_1075_ = lean_array_get(v___x_1045_, v_moduleNames_1074_, v_val_1068_);
lean_dec_ref(v_moduleNames_1074_);
v___x_1107_ = l_Lean_isPrivateName(v_declHint_1042_);
lean_dec(v_declHint_1042_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_array_get_size(v_modules_1073_);
v___x_1109_ = lean_nat_dec_lt(v_val_1068_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_dec_ref(v_modules_1073_);
lean_dec(v_val_1068_);
v___y_1077_ = v___x_1107_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1110_; lean_object* v_toImport_1111_; uint8_t v_isExported_1112_; 
v___x_1110_ = lean_array_fget(v_modules_1073_, v_val_1068_);
lean_dec(v_val_1068_);
lean_dec_ref(v_modules_1073_);
v_toImport_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_toImport_1111_);
lean_dec(v___x_1110_);
v_isExported_1112_ = lean_ctor_get_uint8(v_toImport_1111_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1111_);
v___y_1077_ = v_isExported_1112_;
goto v___jp_1076_;
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v_modules_1073_);
lean_del_object(v___x_1070_);
lean_dec(v_val_1068_);
v___x_1113_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_c_1059_);
v___x_1115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_MessageData_ofName(v_mod_1075_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_MessageData_note(v___x_1120_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_msg_1041_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
v___jp_1076_:
{
if (v___y_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v_c_1059_);
v___x_1080_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_ofName(v_mod_1075_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_MessageData_note(v___x_1085_);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_msg_1041_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1087_);
v___x_1089_ = v___x_1070_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1091_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v_c_1059_);
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_MessageData_ofName(v_mod_1075_);
lean_inc_ref(v___x_1095_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1095_);
v___x_1100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_MessageData_note(v___x_1101_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_msg_1041_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1103_);
v___x_1105_ = v___x_1070_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
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
lean_object* v___x_1125_; 
lean_dec_ref(v_env_1047_);
lean_dec(v_declHint_1042_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_msg_1041_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1126_, lean_object* v_declHint_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1126_, v_declHint_1127_, v___y_1128_);
lean_dec(v___y_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1131_, lean_object* v_declHint_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1148_; 
v___x_1138_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1131_, v_declHint_1132_, v___y_1136_);
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1143_ = l_Lean_unknownIdentifierMessageTag;
v___x_1144_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v_a_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1144_);
v___x_1146_ = v___x_1141_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1149_, lean_object* v_declHint_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1149_, v_declHint_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1157_, lean_object* v_msg_1158_, lean_object* v_declHint_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; lean_object* v_a_1166_; lean_object* v___x_1167_; 
v___x_1165_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1158_, v_declHint_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1157_, v_a_1166_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1168_, lean_object* v_msg_1169_, lean_object* v_declHint_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1168_, v_msg_1169_, v_declHint_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v_ref_1168_);
return v_res_1176_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1183_, lean_object* v_constName_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1190_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1191_ = 0;
lean_inc(v_constName_1184_);
v___x_1192_ = l_Lean_MessageData_ofConstName(v_constName_1184_, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1190_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1183_, v___x_1195_, v_constName_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1197_, lean_object* v_constName_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1197_, v_constName_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v_ref_1197_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_ref_1211_; lean_object* v___x_1212_; 
v_ref_1211_ = lean_ctor_get(v___y_1208_, 2);
v___x_1212_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1211_, v_constName_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v_env_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_st_ref_get(v___y_1224_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_ref(v_env_1227_);
lean_dec(v___x_1226_);
v___x_1228_ = 0;
lean_inc(v_constName_1220_);
v___x_1229_ = l_Lean_Environment_findConstVal_x3f(v_env_1227_, v_constName_1220_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1230_;
}
else
{
lean_object* v_val_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_constName_1220_);
v_val_1231_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1229_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_val_1231_);
lean_dec(v___x_1229_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 0);
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_val_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1246_, lean_object* v_us_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1253_; 
lean_inc(v_c_1246_);
v___x_1253_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1246_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v_levelParams_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v_levelParams_1255_ = lean_ctor_get(v_a_1254_, 1);
v___x_1256_ = l_List_lengthTR___redArg(v_levelParams_1255_);
v___x_1257_ = l_List_lengthTR___redArg(v_us_1247_);
v___x_1258_ = lean_nat_dec_eq(v___x_1256_, v___x_1257_);
lean_dec(v___x_1257_);
lean_dec(v___x_1256_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; 
lean_dec(v_a_1254_);
v___x_1259_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1246_, v_us_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; 
lean_dec(v_c_1246_);
v___x_1260_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1254_, v_us_1247_, v_a_1251_);
return v___x_1260_;
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_us_1247_);
lean_dec(v_c_1246_);
v_a_1261_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1253_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1253_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1269_, lean_object* v_us_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1269_, v_us_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1277_, lean_object* v_constName_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1285_, lean_object* v_constName_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1285_, v_constName_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1293_, lean_object* v_ref_1294_, lean_object* v_constName_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1294_, v_constName_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_ref_1303_, lean_object* v_constName_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1302_, v_ref_1303_, v_constName_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v_ref_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1311_, lean_object* v_ref_1312_, lean_object* v_msg_1313_, lean_object* v_declHint_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1312_, v_msg_1313_, v_declHint_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_ref_1322_, lean_object* v_msg_1323_, lean_object* v_declHint_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1321_, v_ref_1322_, v_msg_1323_, v_declHint_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v_ref_1322_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1331_, lean_object* v_declHint_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1331_, v_declHint_1332_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1339_, lean_object* v_declHint_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1339_, v_declHint_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1347_, lean_object* v_ref_1348_, lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1348_, v_msg_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_ref_1357_, lean_object* v_msg_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1356_, v_ref_1357_, v_msg_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_ref_1357_);
return v_res_1364_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1371_, lean_object* v_idx_1372_, lean_object* v_e_1373_, lean_object* v_a_1374_, lean_object* v_00_u03b1_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1382_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1383_ = l_Lean_mkProj(v_structName_1371_, v_idx_1372_, v_e_1373_);
v___x_1384_ = l_Lean_indentExpr(v___x_1383_);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1382_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_indentExpr(v_a_1374_);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1389_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1391_, lean_object* v_idx_1392_, lean_object* v_e_1393_, lean_object* v_a_1394_, lean_object* v_00_u03b1_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1391_, v_idx_1392_, v_e_1393_, v_a_1394_, v_00_u03b1_1395_, v_x_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v_env_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_st_ref_get(v___y_1407_);
v_env_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc_ref(v_env_1410_);
lean_dec(v___x_1409_);
v___x_1411_ = 0;
lean_inc(v_constName_1403_);
v___x_1412_ = l_Lean_Environment_find_x3f(v_env_1410_, v_constName_1403_, v___x_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1413_;
}
else
{
lean_object* v_val_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_constName_1403_);
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1412_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_val_1414_);
lean_dec(v___x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 0);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_val_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1429_, lean_object* v_structName_1430_, lean_object* v_e_1431_, lean_object* v_idx_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_a_1442_; uint8_t v___x_1446_; 
v___x_1446_ = lean_nat_dec_lt(v_a_1434_, v_upperBound_1429_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_idx_1432_);
lean_dec_ref(v_e_1431_);
lean_dec(v_structName_1430_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1435_);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; 
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
v___x_1448_ = lean_whnf(v_b_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
if (lean_obj_tag(v_a_1449_) == 7)
{
lean_object* v_body_1450_; uint8_t v___x_1451_; 
v_body_1450_ = lean_ctor_get(v_a_1449_, 2);
lean_inc_ref(v_body_1450_);
lean_dec_ref_known(v_a_1449_, 3);
v___x_1451_ = l_Lean_Expr_hasLooseBVars(v_body_1450_);
if (v___x_1451_ == 0)
{
v_a_1442_ = v_body_1450_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_inc_ref(v_e_1431_);
lean_inc(v_a_1434_);
lean_inc(v_structName_1430_);
v___x_1452_ = l_Lean_mkProj(v_structName_1430_, v_a_1434_, v_e_1431_);
v___x_1453_ = lean_expr_instantiate1(v_body_1450_, v___x_1452_);
lean_dec_ref(v___x_1452_);
lean_dec_ref(v_body_1450_);
v_a_1442_ = v___x_1453_;
goto v___jp_1441_;
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1454_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1431_);
lean_inc(v_idx_1432_);
lean_inc(v_structName_1430_);
v___x_1455_ = l_Lean_mkProj(v_structName_1430_, v_idx_1432_, v_e_1431_);
v___x_1456_ = l_Lean_indentExpr(v___x_1455_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
lean_inc_ref(v_a_1433_);
v___x_1460_ = l_Lean_indentExpr(v_a_1433_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1461_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_dec_ref_known(v___x_1462_, 1);
v_a_1442_ = v_a_1449_;
goto v___jp_1441_;
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_a_1449_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_idx_1432_);
lean_dec_ref(v_e_1431_);
lean_dec(v_structName_1430_);
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_idx_1432_);
lean_dec_ref(v_e_1431_);
lean_dec(v_structName_1430_);
return v___x_1448_;
}
}
v___jp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_add(v_a_1434_, v___x_1443_);
lean_dec(v_a_1434_);
v_a_1434_ = v___x_1444_;
v_b_1435_ = v_a_1442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1471_, lean_object* v_structName_1472_, lean_object* v_e_1473_, lean_object* v_idx_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1471_, v_structName_1472_, v_e_1473_, v_idx_1474_, v_a_1475_, v_a_1476_, v_b_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v_upperBound_1471_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1484_, lean_object* v_structName_1485_, lean_object* v_e_1486_, lean_object* v_idx_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_a_1497_; uint8_t v___x_1501_; 
v___x_1501_ = lean_nat_dec_lt(v_a_1489_, v_upperBound_1484_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_idx_1487_);
lean_dec_ref(v_e_1486_);
lean_dec(v_structName_1485_);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_b_1490_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; 
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
v___x_1503_ = lean_whnf(v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref_known(v___x_1503_, 1);
if (lean_obj_tag(v_a_1504_) == 7)
{
lean_object* v_body_1505_; uint8_t v___x_1506_; 
v_body_1505_ = lean_ctor_get(v_a_1504_, 2);
lean_inc_ref(v_body_1505_);
lean_dec_ref_known(v_a_1504_, 3);
v___x_1506_ = l_Lean_Expr_hasLooseBVars(v_body_1505_);
if (v___x_1506_ == 0)
{
v_a_1497_ = v_body_1505_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_inc_ref(v_e_1486_);
lean_inc(v_a_1489_);
lean_inc(v_structName_1485_);
v___x_1507_ = l_Lean_mkProj(v_structName_1485_, v_a_1489_, v_e_1486_);
v___x_1508_ = lean_expr_instantiate1(v_body_1505_, v___x_1507_);
lean_dec_ref(v___x_1507_);
lean_dec_ref(v_body_1505_);
v_a_1497_ = v___x_1508_;
goto v___jp_1496_;
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1509_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1486_);
lean_inc(v_idx_1487_);
lean_inc(v_structName_1485_);
v___x_1510_ = l_Lean_mkProj(v_structName_1485_, v_idx_1487_, v_e_1486_);
v___x_1511_ = l_Lean_indentExpr(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1509_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_inc_ref(v_a_1488_);
v___x_1515_ = l_Lean_indentExpr(v_a_1488_);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1516_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_dec_ref_known(v___x_1517_, 1);
v_a_1497_ = v_a_1504_;
goto v___jp_1496_;
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_a_1504_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_idx_1487_);
lean_dec_ref(v_e_1486_);
lean_dec(v_structName_1485_);
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
else
{
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_idx_1487_);
lean_dec_ref(v_e_1486_);
lean_dec(v_structName_1485_);
return v___x_1503_;
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v_a_1489_, v___x_1498_);
lean_dec(v_a_1489_);
v___x_1500_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1484_, v_structName_1485_, v_e_1486_, v_idx_1487_, v_a_1488_, v___x_1499_, v_a_1497_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1526_, lean_object* v_structName_1527_, lean_object* v_e_1528_, lean_object* v_idx_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1526_, v_structName_1527_, v_e_1528_, v_idx_1529_, v_a_1530_, v_a_1531_, v_b_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v_upperBound_1526_);
return v_res_1538_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1539_; lean_object* v_dummy_1540_; 
v___x_1539_ = lean_box(0);
v_dummy_1540_ = l_Lean_Expr_sort___override(v___x_1539_);
return v_dummy_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1541_, lean_object* v_idx_1542_, lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; 
lean_inc(v_a_1547_);
lean_inc_ref(v_a_1546_);
lean_inc(v_a_1545_);
lean_inc_ref(v_a_1544_);
lean_inc_ref(v_e_1543_);
v___x_1549_ = lean_infer_type(v_e_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
lean_inc(v_a_1547_);
lean_inc_ref(v_a_1546_);
lean_inc(v_a_1545_);
lean_inc_ref(v_a_1544_);
v___x_1551_ = lean_whnf(v_a_1550_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = l_Lean_Expr_getAppFn(v_a_1552_);
if (lean_obj_tag(v___x_1553_) == 4)
{
lean_object* v_declName_1554_; lean_object* v_us_1555_; lean_object* v___x_1556_; lean_object* v_env_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; 
v_declName_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_declName_1554_);
v_us_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_us_1555_);
lean_dec_ref_known(v___x_1553_, 2);
v___x_1556_ = lean_st_ref_get(v_a_1547_);
v_env_1560_ = lean_ctor_get(v___x_1556_, 0);
lean_inc_ref(v_env_1560_);
lean_dec(v___x_1556_);
v___x_1561_ = 0;
v___x_1562_ = l_Lean_Environment_find_x3f(v_env_1560_, v_declName_1554_, v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec(v_us_1555_);
v___x_1563_ = lean_box(0);
v___x_1564_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1563_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1564_;
}
else
{
lean_object* v_val_1565_; 
v_val_1565_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v___x_1562_, 1);
if (lean_obj_tag(v_val_1565_) == 5)
{
lean_object* v_val_1566_; lean_object* v_ctors_1567_; 
v_val_1566_ = lean_ctor_get(v_val_1565_, 0);
lean_inc_ref(v_val_1566_);
lean_dec_ref_known(v_val_1565_, 1);
v_ctors_1567_ = lean_ctor_get(v_val_1566_, 4);
lean_inc(v_ctors_1567_);
if (lean_obj_tag(v_ctors_1567_) == 1)
{
lean_object* v_tail_1568_; 
v_tail_1568_ = lean_ctor_get(v_ctors_1567_, 1);
if (lean_obj_tag(v_tail_1568_) == 0)
{
lean_object* v_toConstantVal_1569_; lean_object* v_numParams_1570_; lean_object* v_numIndices_1571_; lean_object* v_head_1572_; lean_object* v___x_1573_; 
v_toConstantVal_1569_ = lean_ctor_get(v_val_1566_, 0);
lean_inc_ref(v_toConstantVal_1569_);
v_numParams_1570_ = lean_ctor_get(v_val_1566_, 1);
lean_inc(v_numParams_1570_);
v_numIndices_1571_ = lean_ctor_get(v_val_1566_, 2);
lean_inc(v_numIndices_1571_);
lean_dec_ref(v_val_1566_);
v_head_1572_ = lean_ctor_get(v_ctors_1567_, 0);
lean_inc(v_head_1572_);
lean_dec_ref_known(v_ctors_1567_, 2);
v___x_1573_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1572_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
if (lean_obj_tag(v_a_1574_) == 6)
{
lean_object* v_val_1575_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v_name_1615_; uint8_t v___x_1616_; 
v_val_1575_ = lean_ctor_get(v_a_1574_, 0);
lean_inc_ref(v_val_1575_);
lean_dec_ref_known(v_a_1574_, 1);
v_name_1615_ = lean_ctor_get(v_toConstantVal_1569_, 0);
lean_inc(v_name_1615_);
lean_dec_ref(v_toConstantVal_1569_);
v___x_1616_ = lean_name_eq(v_name_1615_, v_structName_1541_);
lean_dec(v_name_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_val_1575_);
lean_dec(v_numIndices_1571_);
lean_dec(v_numParams_1570_);
lean_dec(v_us_1555_);
v___x_1617_ = lean_box(0);
v___x_1618_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1617_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
v___y_1577_ = v_a_1544_;
v___y_1578_ = v_a_1545_;
v___y_1579_ = v_a_1546_;
v___y_1580_ = v_a_1547_;
goto v___jp_1576_;
}
v___jp_1576_:
{
lean_object* v_dummy_1581_; lean_object* v_nargs_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_dummy_1581_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1582_ = l_Lean_Expr_getAppNumArgs(v_a_1552_);
lean_inc(v_nargs_1582_);
v___x_1583_ = lean_mk_array(v_nargs_1582_, v_dummy_1581_);
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = lean_nat_sub(v_nargs_1582_, v___x_1584_);
lean_dec(v_nargs_1582_);
lean_inc(v_a_1552_);
v___x_1586_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1552_, v___x_1583_, v___x_1585_);
v___x_1587_ = lean_nat_add(v_numParams_1570_, v_numIndices_1571_);
lean_dec(v_numIndices_1571_);
v___x_1588_ = lean_array_get_size(v___x_1586_);
v___x_1589_ = lean_nat_dec_eq(v___x_1587_, v___x_1588_);
lean_dec(v___x_1587_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec_ref(v___x_1586_);
lean_dec_ref(v_val_1575_);
lean_dec(v_numParams_1570_);
lean_dec(v_us_1555_);
v___x_1590_ = lean_box(0);
v___x_1591_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1590_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1591_;
}
else
{
lean_object* v_toConstantVal_1592_; lean_object* v_name_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_toConstantVal_1592_ = lean_ctor_get(v_val_1575_, 0);
lean_inc_ref(v_toConstantVal_1592_);
lean_dec_ref(v_val_1575_);
v_name_1593_ = lean_ctor_get(v_toConstantVal_1592_, 0);
lean_inc(v_name_1593_);
lean_dec_ref(v_toConstantVal_1592_);
v___x_1594_ = l_Lean_mkConst(v_name_1593_, v_us_1555_);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = l_Array_toSubarray___redArg(v___x_1586_, v___x_1595_, v_numParams_1570_);
v___x_1597_ = l_Subarray_copy___redArg(v___x_1596_);
v___x_1598_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1594_, v___x_1597_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec_ref(v___x_1597_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
lean_inc(v_a_1552_);
lean_inc_ref(v_e_1543_);
lean_inc(v_structName_1541_);
lean_inc(v_idx_1542_);
v___x_1600_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1542_, v_structName_1541_, v_e_1543_, v_idx_1542_, v_a_1552_, v___x_1595_, v_a_1599_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1577_);
v___x_1602_ = lean_whnf(v_a_1601_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1614_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1614_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1614_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
if (lean_obj_tag(v_a_1603_) == 7)
{
lean_object* v_binderType_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_dec(v_a_1552_);
lean_dec_ref(v_e_1543_);
lean_dec(v_idx_1542_);
lean_dec(v_structName_1541_);
v_binderType_1607_ = lean_ctor_get(v_a_1603_, 1);
lean_inc_ref(v_binderType_1607_);
lean_dec_ref_known(v_a_1603_, 3);
v___x_1608_ = lean_expr_consume_type_annotations(v_binderType_1607_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1608_);
v___x_1610_ = v___x_1605_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_del_object(v___x_1605_);
lean_dec(v_a_1603_);
v___x_1612_ = lean_box(0);
v___x_1613_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1612_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1613_;
}
}
}
else
{
lean_dec(v_a_1552_);
lean_dec_ref(v_e_1543_);
lean_dec(v_idx_1542_);
lean_dec(v_structName_1541_);
return v___x_1602_;
}
}
else
{
lean_dec(v_a_1552_);
lean_dec_ref(v_e_1543_);
lean_dec(v_idx_1542_);
lean_dec(v_structName_1541_);
return v___x_1600_;
}
}
else
{
lean_dec(v_a_1552_);
lean_dec_ref(v_e_1543_);
lean_dec(v_idx_1542_);
lean_dec(v_structName_1541_);
return v___x_1598_;
}
}
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec(v_a_1574_);
lean_dec(v_numIndices_1571_);
lean_dec(v_numParams_1570_);
lean_dec_ref(v_toConstantVal_1569_);
lean_dec(v_us_1555_);
v___x_1627_ = lean_box(0);
v___x_1628_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1627_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1628_;
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_numIndices_1571_);
lean_dec(v_numParams_1570_);
lean_dec_ref(v_toConstantVal_1569_);
lean_dec(v_us_1555_);
lean_dec(v_a_1552_);
lean_dec_ref(v_e_1543_);
lean_dec(v_idx_1542_);
lean_dec(v_structName_1541_);
v_a_1629_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1573_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1573_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1567_, 2);
lean_dec_ref(v_val_1566_);
lean_dec(v_us_1555_);
goto v___jp_1557_;
}
}
else
{
lean_dec(v_ctors_1567_);
lean_dec_ref(v_val_1566_);
lean_dec(v_us_1555_);
goto v___jp_1557_;
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec(v_val_1565_);
lean_dec(v_us_1555_);
v___x_1637_ = lean_box(0);
v___x_1638_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1637_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1638_;
}
}
v___jp_1557_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_box(0);
v___x_1559_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1558_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1559_;
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v___x_1553_);
v___x_1639_ = lean_box(0);
v___x_1640_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1541_, v_idx_1542_, v_e_1543_, v_a_1552_, lean_box(0), v___x_1639_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
return v___x_1640_;
}
}
else
{
lean_dec_ref(v_e_1543_);
lean_dec(v_idx_1542_);
lean_dec(v_structName_1541_);
return v___x_1551_;
}
}
else
{
lean_dec_ref(v_e_1543_);
lean_dec(v_idx_1542_);
lean_dec(v_structName_1541_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1641_, lean_object* v_idx_1642_, lean_object* v_e_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1641_, v_idx_1642_, v_e_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1650_, lean_object* v_structName_1651_, lean_object* v_e_1652_, lean_object* v_idx_1653_, lean_object* v_a_1654_, lean_object* v_inst_1655_, lean_object* v_R_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_, lean_object* v_c_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1650_, v_structName_1651_, v_e_1652_, v_idx_1653_, v_a_1654_, v_a_1657_, v_b_1658_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1666_, lean_object* v_structName_1667_, lean_object* v_e_1668_, lean_object* v_idx_1669_, lean_object* v_a_1670_, lean_object* v_inst_1671_, lean_object* v_R_1672_, lean_object* v_a_1673_, lean_object* v_b_1674_, lean_object* v_c_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1666_, v_structName_1667_, v_e_1668_, v_idx_1669_, v_a_1670_, v_inst_1671_, v_R_1672_, v_a_1673_, v_b_1674_, v_c_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v_upperBound_1666_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1682_, lean_object* v_structName_1683_, lean_object* v_e_1684_, lean_object* v_idx_1685_, lean_object* v_a_1686_, lean_object* v_inst_1687_, lean_object* v_R_1688_, lean_object* v_a_1689_, lean_object* v_b_1690_, lean_object* v_c_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1682_, v_structName_1683_, v_e_1684_, v_idx_1685_, v_a_1686_, v_a_1689_, v_b_1690_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1698_, lean_object* v_structName_1699_, lean_object* v_e_1700_, lean_object* v_idx_1701_, lean_object* v_a_1702_, lean_object* v_inst_1703_, lean_object* v_R_1704_, lean_object* v_a_1705_, lean_object* v_b_1706_, lean_object* v_c_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1698_, v_structName_1699_, v_e_1700_, v_idx_1701_, v_a_1702_, v_inst_1703_, v_R_1704_, v_a_1705_, v_b_1706_, v_c_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v_upperBound_1698_);
return v_res_1713_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1723_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1724_ = l_Lean_indentExpr(v_type_1717_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1725_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1734_, lean_object* v_type_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_type_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1742_, v_type_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v_ks_1754_; lean_object* v_vs_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1779_; 
v_ks_1754_ = lean_ctor_get(v_x_1750_, 0);
v_vs_1755_ = lean_ctor_get(v_x_1750_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_x_1750_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1757_ = v_x_1750_;
v_isShared_1758_ = v_isSharedCheck_1779_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_vs_1755_);
lean_inc(v_ks_1754_);
lean_dec(v_x_1750_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1779_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_array_get_size(v_ks_1754_);
v___x_1760_ = lean_nat_dec_lt(v_x_1751_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec(v_x_1751_);
v___x_1761_ = lean_array_push(v_ks_1754_, v_x_1752_);
v___x_1762_ = lean_array_push(v_vs_1755_, v_x_1753_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1762_);
lean_ctor_set(v___x_1757_, 0, v___x_1761_);
v___x_1764_ = v___x_1757_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v_k_x27_1766_; uint8_t v___x_1767_; 
v_k_x27_1766_ = lean_array_fget_borrowed(v_ks_1754_, v_x_1751_);
v___x_1767_ = l_Lean_instBEqMVarId_beq(v_x_1752_, v_k_x27_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1769_; 
if (v_isShared_1758_ == 0)
{
v___x_1769_ = v___x_1757_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_ks_1754_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_vs_1755_);
v___x_1769_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_add(v_x_1751_, v___x_1770_);
lean_dec(v_x_1751_);
v_x_1750_ = v___x_1769_;
v_x_1751_ = v___x_1771_;
goto _start;
}
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1774_ = lean_array_fset(v_ks_1754_, v_x_1751_, v_x_1752_);
v___x_1775_ = lean_array_fset(v_vs_1755_, v_x_1751_, v_x_1753_);
lean_dec(v_x_1751_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1775_);
lean_ctor_set(v___x_1757_, 0, v___x_1774_);
v___x_1777_ = v___x_1757_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1780_, lean_object* v_k_1781_, lean_object* v_v_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1780_, v___x_1783_, v_k_1781_, v_v_1782_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1786_, size_t v_x_1787_, size_t v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1786_) == 0)
{
lean_object* v_es_1791_; size_t v___x_1792_; size_t v___x_1793_; lean_object* v_j_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_es_1791_ = lean_ctor_get(v_x_1786_, 0);
v___x_1792_ = ((size_t)31ULL);
v___x_1793_ = lean_usize_land(v_x_1787_, v___x_1792_);
v_j_1794_ = lean_usize_to_nat(v___x_1793_);
v___x_1795_ = lean_array_get_size(v_es_1791_);
v___x_1796_ = lean_nat_dec_lt(v_j_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_dec(v_j_1794_);
lean_dec(v_x_1790_);
lean_dec(v_x_1789_);
return v_x_1786_;
}
else
{
lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1835_; 
lean_inc_ref(v_es_1791_);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_x_1786_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v_x_1786_, 0);
lean_dec(v_unused_1836_);
v___x_1798_ = v_x_1786_;
v_isShared_1799_ = v_isSharedCheck_1835_;
goto v_resetjp_1797_;
}
else
{
lean_dec(v_x_1786_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1835_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_v_1800_; lean_object* v___x_1801_; lean_object* v_xs_x27_1802_; lean_object* v___y_1804_; 
v_v_1800_ = lean_array_fget(v_es_1791_, v_j_1794_);
v___x_1801_ = lean_box(0);
v_xs_x27_1802_ = lean_array_fset(v_es_1791_, v_j_1794_, v___x_1801_);
switch(lean_obj_tag(v_v_1800_))
{
case 0:
{
lean_object* v_key_1809_; lean_object* v_val_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1820_; 
v_key_1809_ = lean_ctor_get(v_v_1800_, 0);
v_val_1810_ = lean_ctor_get(v_v_1800_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_v_1800_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1812_ = v_v_1800_;
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_val_1810_);
lean_inc(v_key_1809_);
lean_dec(v_v_1800_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Lean_instBEqMVarId_beq(v_x_1789_, v_key_1809_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_del_object(v___x_1812_);
v___x_1815_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1809_, v_val_1810_, v_x_1789_, v_x_1790_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
v___y_1804_ = v___x_1816_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_val_1810_);
lean_dec(v_key_1809_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 1, v_x_1790_);
lean_ctor_set(v___x_1812_, 0, v_x_1789_);
v___x_1818_ = v___x_1812_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_x_1789_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_x_1790_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v___y_1804_ = v___x_1818_;
goto v___jp_1803_;
}
}
}
}
case 1:
{
lean_object* v_node_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1833_; 
v_node_1821_ = lean_ctor_get(v_v_1800_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_v_1800_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1823_ = v_v_1800_;
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_node_1821_);
lean_dec(v_v_1800_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
size_t v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1825_ = ((size_t)5ULL);
v___x_1826_ = lean_usize_shift_right(v_x_1787_, v___x_1825_);
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_add(v_x_1788_, v___x_1827_);
v___x_1829_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1821_, v___x_1826_, v___x_1828_, v_x_1789_, v_x_1790_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1829_);
v___x_1831_ = v___x_1823_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
v___y_1804_ = v___x_1831_;
goto v___jp_1803_;
}
}
}
default: 
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_x_1789_);
lean_ctor_set(v___x_1834_, 1, v_x_1790_);
v___y_1804_ = v___x_1834_;
goto v___jp_1803_;
}
}
v___jp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = lean_array_fset(v_xs_x27_1802_, v_j_1794_, v___y_1804_);
lean_dec(v_j_1794_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1805_);
v___x_1807_ = v___x_1798_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
else
{
lean_object* v_ks_1837_; lean_object* v_vs_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1856_; 
v_ks_1837_ = lean_ctor_get(v_x_1786_, 0);
v_vs_1838_ = lean_ctor_get(v_x_1786_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_x_1786_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1840_ = v_x_1786_;
v_isShared_1841_ = v_isSharedCheck_1856_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_vs_1838_);
lean_inc(v_ks_1837_);
lean_dec(v_x_1786_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1856_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_ks_1837_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_vs_1838_);
v___x_1843_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v_newNode_1844_; size_t v___x_1845_; uint8_t v___x_1846_; 
v_newNode_1844_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1843_, v_x_1789_, v_x_1790_);
v___x_1845_ = ((size_t)7ULL);
v___x_1846_ = lean_usize_dec_le(v___x_1845_, v_x_1788_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1847_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1844_);
v___x_1848_ = lean_unsigned_to_nat(4u);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
lean_dec(v___x_1847_);
if (v___x_1849_ == 0)
{
lean_object* v_ks_1850_; lean_object* v_vs_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_ks_1850_ = lean_ctor_get(v_newNode_1844_, 0);
lean_inc_ref(v_ks_1850_);
v_vs_1851_ = lean_ctor_get(v_newNode_1844_, 1);
lean_inc_ref(v_vs_1851_);
lean_dec_ref(v_newNode_1844_);
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1788_, v_ks_1850_, v_vs_1851_, v___x_1852_, v___x_1853_);
lean_dec_ref(v_vs_1851_);
lean_dec_ref(v_ks_1850_);
return v___x_1854_;
}
else
{
return v_newNode_1844_;
}
}
else
{
return v_newNode_1844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1857_, lean_object* v_keys_1858_, lean_object* v_vals_1859_, lean_object* v_i_1860_, lean_object* v_entries_1861_){
_start:
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_array_get_size(v_keys_1858_);
v___x_1863_ = lean_nat_dec_lt(v_i_1860_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec(v_i_1860_);
return v_entries_1861_;
}
else
{
lean_object* v_k_1864_; lean_object* v_v_1865_; uint64_t v___x_1866_; size_t v_h_1867_; size_t v___x_1868_; lean_object* v___x_1869_; size_t v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; size_t v_h_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_k_1864_ = lean_array_fget_borrowed(v_keys_1858_, v_i_1860_);
v_v_1865_ = lean_array_fget_borrowed(v_vals_1859_, v_i_1860_);
v___x_1866_ = l_Lean_instHashableMVarId_hash(v_k_1864_);
v_h_1867_ = lean_uint64_to_usize(v___x_1866_);
v___x_1868_ = ((size_t)5ULL);
v___x_1869_ = lean_unsigned_to_nat(1u);
v___x_1870_ = ((size_t)1ULL);
v___x_1871_ = lean_usize_sub(v_depth_1857_, v___x_1870_);
v___x_1872_ = lean_usize_mul(v___x_1868_, v___x_1871_);
v_h_1873_ = lean_usize_shift_right(v_h_1867_, v___x_1872_);
v___x_1874_ = lean_nat_add(v_i_1860_, v___x_1869_);
lean_dec(v_i_1860_);
lean_inc(v_v_1865_);
lean_inc(v_k_1864_);
v___x_1875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1861_, v_h_1873_, v_depth_1857_, v_k_1864_, v_v_1865_);
v_i_1860_ = v___x_1874_;
v_entries_1861_ = v___x_1875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1877_, lean_object* v_keys_1878_, lean_object* v_vals_1879_, lean_object* v_i_1880_, lean_object* v_entries_1881_){
_start:
{
size_t v_depth_boxed_1882_; lean_object* v_res_1883_; 
v_depth_boxed_1882_ = lean_unbox_usize(v_depth_1877_);
lean_dec(v_depth_1877_);
v_res_1883_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1882_, v_keys_1878_, v_vals_1879_, v_i_1880_, v_entries_1881_);
lean_dec_ref(v_vals_1879_);
lean_dec_ref(v_keys_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
size_t v_x_1155__boxed_1889_; size_t v_x_1156__boxed_1890_; lean_object* v_res_1891_; 
v_x_1155__boxed_1889_ = lean_unbox_usize(v_x_1885_);
lean_dec(v_x_1885_);
v_x_1156__boxed_1890_ = lean_unbox_usize(v_x_1886_);
lean_dec(v_x_1886_);
v_res_1891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1884_, v_x_1155__boxed_1889_, v_x_1156__boxed_1890_, v_x_1887_, v_x_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
uint64_t v___x_1895_; size_t v___x_1896_; size_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1895_ = l_Lean_instHashableMVarId_hash(v_x_1893_);
v___x_1896_ = lean_uint64_to_usize(v___x_1895_);
v___x_1897_ = ((size_t)1ULL);
v___x_1898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1892_, v___x_1896_, v___x_1897_, v_x_1893_, v_x_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1899_, lean_object* v_val_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; lean_object* v_mctx_1904_; lean_object* v_cache_1905_; lean_object* v_zetaDeltaFVarIds_1906_; lean_object* v_postponed_1907_; lean_object* v_diag_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1938_; 
v___x_1903_ = lean_st_ref_take(v___y_1901_);
v_mctx_1904_ = lean_ctor_get(v___x_1903_, 0);
v_cache_1905_ = lean_ctor_get(v___x_1903_, 1);
v_zetaDeltaFVarIds_1906_ = lean_ctor_get(v___x_1903_, 2);
v_postponed_1907_ = lean_ctor_get(v___x_1903_, 3);
v_diag_1908_ = lean_ctor_get(v___x_1903_, 4);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1910_ = v___x_1903_;
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_diag_1908_);
lean_inc(v_postponed_1907_);
lean_inc(v_zetaDeltaFVarIds_1906_);
lean_inc(v_cache_1905_);
lean_inc(v_mctx_1904_);
lean_dec(v___x_1903_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_depth_1912_; lean_object* v_levelAssignDepth_1913_; lean_object* v_lmvarCounter_1914_; lean_object* v_mvarCounter_1915_; lean_object* v_lDecls_1916_; lean_object* v_decls_1917_; lean_object* v_userNames_1918_; lean_object* v_lAssignment_1919_; lean_object* v_eAssignment_1920_; lean_object* v_dAssignment_1921_; lean_object* v_instanceTypedMVars_1922_; lean_object* v_synthNormMemo_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1937_; 
v_depth_1912_ = lean_ctor_get(v_mctx_1904_, 0);
v_levelAssignDepth_1913_ = lean_ctor_get(v_mctx_1904_, 1);
v_lmvarCounter_1914_ = lean_ctor_get(v_mctx_1904_, 2);
v_mvarCounter_1915_ = lean_ctor_get(v_mctx_1904_, 3);
v_lDecls_1916_ = lean_ctor_get(v_mctx_1904_, 4);
v_decls_1917_ = lean_ctor_get(v_mctx_1904_, 5);
v_userNames_1918_ = lean_ctor_get(v_mctx_1904_, 6);
v_lAssignment_1919_ = lean_ctor_get(v_mctx_1904_, 7);
v_eAssignment_1920_ = lean_ctor_get(v_mctx_1904_, 8);
v_dAssignment_1921_ = lean_ctor_get(v_mctx_1904_, 9);
v_instanceTypedMVars_1922_ = lean_ctor_get(v_mctx_1904_, 10);
v_synthNormMemo_1923_ = lean_ctor_get(v_mctx_1904_, 11);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_mctx_1904_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1925_ = v_mctx_1904_;
v_isShared_1926_ = v_isSharedCheck_1937_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_synthNormMemo_1923_);
lean_inc(v_instanceTypedMVars_1922_);
lean_inc(v_dAssignment_1921_);
lean_inc(v_eAssignment_1920_);
lean_inc(v_lAssignment_1919_);
lean_inc(v_userNames_1918_);
lean_inc(v_decls_1917_);
lean_inc(v_lDecls_1916_);
lean_inc(v_mvarCounter_1915_);
lean_inc(v_lmvarCounter_1914_);
lean_inc(v_levelAssignDepth_1913_);
lean_inc(v_depth_1912_);
lean_dec(v_mctx_1904_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1937_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1920_, v_mvarId_1899_, v_val_1900_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 8, v___x_1928_);
v___x_1930_ = v___x_1925_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_depth_1912_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_levelAssignDepth_1913_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_lmvarCounter_1914_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_mvarCounter_1915_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v_lDecls_1916_);
lean_ctor_set(v_reuseFailAlloc_1936_, 5, v_decls_1917_);
lean_ctor_set(v_reuseFailAlloc_1936_, 6, v_userNames_1918_);
lean_ctor_set(v_reuseFailAlloc_1936_, 7, v_lAssignment_1919_);
lean_ctor_set(v_reuseFailAlloc_1936_, 8, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1936_, 9, v_dAssignment_1921_);
lean_ctor_set(v_reuseFailAlloc_1936_, 10, v_instanceTypedMVars_1922_);
lean_ctor_set(v_reuseFailAlloc_1936_, 11, v_synthNormMemo_1923_);
v___x_1930_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1932_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1930_);
v___x_1932_ = v___x_1910_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_cache_1905_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_zetaDeltaFVarIds_1906_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_postponed_1907_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_diag_1908_);
v___x_1932_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_st_ref_put(v___y_1901_, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1927_);
return v___x_1934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1939_, lean_object* v_val_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1939_, v_val_1940_, v___y_1941_);
lean_dec(v___y_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; 
lean_inc(v_a_1948_);
lean_inc_ref(v_a_1947_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc_ref(v_type_1944_);
v___x_1950_ = lean_infer_type(v_type_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = l_Lean_Meta_whnfD(v_a_1951_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1987_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1987_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1987_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
switch(lean_obj_tag(v_a_1953_))
{
case 3:
{
lean_object* v_u_1957_; lean_object* v___x_1959_; 
lean_dec_ref(v_type_1944_);
v_u_1957_ = lean_ctor_get(v_a_1953_, 0);
lean_inc(v_u_1957_);
lean_dec_ref_known(v_a_1953_, 1);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v_u_1957_);
v___x_1959_ = v___x_1955_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_u_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
case 2:
{
lean_object* v_mvarId_1961_; lean_object* v___x_1962_; 
lean_del_object(v___x_1955_);
v_mvarId_1961_ = lean_ctor_get(v_a_1953_, 0);
lean_inc_n(v_mvarId_1961_, 2);
lean_dec_ref_known(v_a_1953_, 1);
v___x_1962_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1961_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; uint8_t v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = lean_unbox(v_a_1963_);
lean_dec(v_a_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref(v_type_1944_);
v___x_1965_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc_n(v_a_1966_, 2);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1967_ = l_Lean_mkSort(v_a_1966_);
v___x_1968_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1961_, v___x_1967_, v_a_1946_);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v___x_1968_, 0);
lean_dec(v_unused_1976_);
v___x_1970_ = v___x_1968_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_dec(v___x_1968_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_a_1966_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1966_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
else
{
lean_dec(v_mvarId_1961_);
return v___x_1965_;
}
}
else
{
lean_object* v___x_1977_; 
lean_dec(v_mvarId_1961_);
v___x_1977_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1977_;
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_mvarId_1961_);
lean_dec_ref(v_type_1944_);
v_a_1978_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1962_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1962_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
default: 
{
lean_object* v___x_1986_; 
lean_del_object(v___x_1955_);
lean_dec(v_a_1953_);
v___x_1986_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_type_1944_);
v_a_1988_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1952_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1952_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_type_1944_);
v_a_1996_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1950_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1950_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Meta_getLevel(v_type_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_2011_, lean_object* v_val_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2011_, v_val_2012_, v___y_2014_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_2019_, lean_object* v_val_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_2019_, v_val_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2028_, v_x_2029_, v_x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2032_, lean_object* v_x_2033_, size_t v_x_2034_, size_t v_x_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2033_, v_x_2034_, v_x_2035_, v_x_2036_, v_x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
size_t v_x_1504__boxed_2045_; size_t v_x_1505__boxed_2046_; lean_object* v_res_2047_; 
v_x_1504__boxed_2045_ = lean_unbox_usize(v_x_2041_);
lean_dec(v_x_2041_);
v_x_1505__boxed_2046_ = lean_unbox_usize(v_x_2042_);
lean_dec(v_x_2042_);
v_res_2047_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2039_, v_x_2040_, v_x_1504__boxed_2045_, v_x_1505__boxed_2046_, v_x_2043_, v_x_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2048_, lean_object* v_n_2049_, lean_object* v_k_2050_, lean_object* v_v_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2049_, v_k_2050_, v_v_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2053_, size_t v_depth_2054_, lean_object* v_keys_2055_, lean_object* v_vals_2056_, lean_object* v_heq_2057_, lean_object* v_i_2058_, lean_object* v_entries_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2054_, v_keys_2055_, v_vals_2056_, v_i_2058_, v_entries_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2061_, lean_object* v_depth_2062_, lean_object* v_keys_2063_, lean_object* v_vals_2064_, lean_object* v_heq_2065_, lean_object* v_i_2066_, lean_object* v_entries_2067_){
_start:
{
size_t v_depth_boxed_2068_; lean_object* v_res_2069_; 
v_depth_boxed_2068_ = lean_unbox_usize(v_depth_2062_);
lean_dec(v_depth_2062_);
v_res_2069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2061_, v_depth_boxed_2068_, v_keys_2063_, v_vals_2064_, v_heq_2065_, v_i_2066_, v_entries_2067_);
lean_dec_ref(v_vals_2064_);
lean_dec_ref(v_keys_2063_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2071_, v_x_2072_, v_x_2073_, v_x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2076_, lean_object* v_b_2077_, lean_object* v_c_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
v___x_2084_ = lean_apply_7(v_k_2076_, v_b_2077_, v_c_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, lean_box(0));
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2085_, lean_object* v_b_2086_, lean_object* v_c_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2085_, v_b_2086_, v_c_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2094_, lean_object* v_k_2095_, uint8_t v_cleanupAnnotations_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___f_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___f_2102_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2102_, 0, v_k_2095_);
v___x_2103_ = 0;
v___x_2104_ = lean_box(0);
v___x_2105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2103_, v___x_2104_, v_type_2094_, v___f_2102_, v_cleanupAnnotations_2096_, v___x_2103_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_a_2114_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2105_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2105_);
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
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2122_, lean_object* v_k_2123_, lean_object* v_cleanupAnnotations_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2130_; lean_object* v_res_2131_; 
v_cleanupAnnotations_boxed_2130_ = lean_unbox(v_cleanupAnnotations_2124_);
v_res_2131_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2122_, v_k_2123_, v_cleanupAnnotations_boxed_2130_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2132_, lean_object* v_type_2133_, lean_object* v_k_2134_, uint8_t v_cleanupAnnotations_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2133_, v_k_2134_, v_cleanupAnnotations_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_type_2143_, lean_object* v_k_2144_, lean_object* v_cleanupAnnotations_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2151_; lean_object* v_res_2152_; 
v_cleanupAnnotations_boxed_2151_ = lean_unbox(v_cleanupAnnotations_2145_);
v_res_2152_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2142_, v_type_2143_, v_k_2144_, v_cleanupAnnotations_boxed_2151_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2153_, size_t v_i_2154_, size_t v_stop_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_usize_dec_eq(v_i_2154_, v_stop_2155_);
if (v___x_2162_ == 0)
{
size_t v___x_2163_; size_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = ((size_t)1ULL);
v___x_2164_ = lean_usize_sub(v_i_2154_, v___x_2163_);
v___x_2165_ = lean_array_uget_borrowed(v_as_2153_, v___x_2164_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
lean_inc(v___x_2165_);
v___x_2166_ = lean_infer_type(v___x_2165_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = l_Lean_Meta_getLevel(v_a_2167_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = l_Lean_mkLevelIMax_x27(v_a_2169_, v_b_2156_);
v_i_2154_ = v___x_2164_;
v_b_2156_ = v___x_2170_;
goto _start;
}
else
{
lean_dec(v_b_2156_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2172_; 
v_a_2172_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2168_, 1);
v_i_2154_ = v___x_2164_;
v_b_2156_ = v_a_2172_;
goto _start;
}
else
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_b_2156_);
v_a_2174_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2166_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2166_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_b_2156_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2183_, lean_object* v_i_2184_, lean_object* v_stop_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
size_t v_i_boxed_2192_; size_t v_stop_boxed_2193_; lean_object* v_res_2194_; 
v_i_boxed_2192_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_stop_boxed_2193_ = lean_unbox_usize(v_stop_2185_);
lean_dec(v_stop_2185_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2183_, v_i_boxed_2192_, v_stop_boxed_2193_, v_b_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec_ref(v_as_2183_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2195_, lean_object* v_e_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___y_2203_; lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_Meta_getLevel(v_e_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v___x_2224_ = lean_array_get_size(v_xs_2195_);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_nat_dec_lt(v___x_2225_, v___x_2224_);
if (v___x_2226_ == 0)
{
v___y_2203_ = v___x_2222_;
goto v___jp_2202_;
}
else
{
size_t v___x_2227_; size_t v___x_2228_; lean_object* v___x_2229_; 
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v___x_2227_ = lean_usize_of_nat(v___x_2224_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2195_, v___x_2227_, v___x_2228_, v_a_2223_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
v___y_2203_ = v___x_2229_;
goto v___jp_2202_;
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2222_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2222_);
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
v___jp_2202_:
{
if (lean_obj_tag(v___y_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2213_; 
v_a_2204_ = lean_ctor_get(v___y_2203_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___y_2203_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2206_ = v___y_2203_;
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___y_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2213_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2208_ = l_Lean_Level_normalize(v_a_2204_);
lean_dec(v_a_2204_);
v___x_2209_ = l_Lean_mkSort(v___x_2208_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2209_);
v___x_2211_ = v___x_2206_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___y_2203_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___y_2203_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___y_2203_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___y_2203_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
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
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2642_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2642_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2642_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2589_; lean_object* v_cache_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2637_; 
v___x_2589_ = lean_st_ref_get(v_a_2497_);
v_cache_2590_ = lean_ctor_get(v___x_2589_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; lean_object* v_unused_2639_; lean_object* v_unused_2640_; lean_object* v_unused_2641_; 
v_unused_2638_ = lean_ctor_get(v___x_2589_, 4);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v___x_2589_, 3);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v___x_2589_, 2);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v___x_2589_, 0);
lean_dec(v_unused_2641_);
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2637_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_cache_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2637_;
goto v_resetjp_2591_;
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
lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2587_; 
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v___x_2550_, 0);
lean_dec(v_unused_2588_);
v___x_2554_ = v___x_2550_;
v_isShared_2555_ = v_isSharedCheck_2587_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v___x_2550_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2587_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v_cache_2557_; lean_object* v_mctx_2558_; lean_object* v_zetaDeltaFVarIds_2559_; lean_object* v_postponed_2560_; lean_object* v_diag_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2586_; 
v___x_2556_ = lean_st_ref_take(v_a_2497_);
v_cache_2557_ = lean_ctor_get(v___x_2556_, 1);
v_mctx_2558_ = lean_ctor_get(v___x_2556_, 0);
v_zetaDeltaFVarIds_2559_ = lean_ctor_get(v___x_2556_, 2);
v_postponed_2560_ = lean_ctor_get(v___x_2556_, 3);
v_diag_2561_ = lean_ctor_get(v___x_2556_, 4);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2563_ = v___x_2556_;
v_isShared_2564_ = v_isSharedCheck_2586_;
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
v_isShared_2564_ = v_isSharedCheck_2586_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_inferType_2565_; lean_object* v_funInfo_2566_; lean_object* v_synthInstance_2567_; lean_object* v_whnf_2568_; lean_object* v_defEqTrans_2569_; lean_object* v_defEqPerm_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2585_; 
v_inferType_2565_ = lean_ctor_get(v_cache_2557_, 0);
v_funInfo_2566_ = lean_ctor_get(v_cache_2557_, 1);
v_synthInstance_2567_ = lean_ctor_get(v_cache_2557_, 2);
v_whnf_2568_ = lean_ctor_get(v_cache_2557_, 3);
v_defEqTrans_2569_ = lean_ctor_get(v_cache_2557_, 4);
v_defEqPerm_2570_ = lean_ctor_get(v_cache_2557_, 5);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_cache_2557_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2572_ = v_cache_2557_;
v_isShared_2573_ = v_isSharedCheck_2585_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_defEqPerm_2570_);
lean_inc(v_defEqTrans_2569_);
lean_inc(v_whnf_2568_);
lean_inc(v_synthInstance_2567_);
lean_inc(v_funInfo_2566_);
lean_inc(v_inferType_2565_);
lean_dec(v_cache_2557_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2585_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_inc(v_a_2551_);
v___x_2574_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2542_, v___x_2543_, v_inferType_2565_, v_a_2545_, v_a_2551_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2574_);
v___x_2576_ = v___x_2572_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_funInfo_2566_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_synthInstance_2567_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_whnf_2568_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_defEqTrans_2569_);
lean_ctor_set(v_reuseFailAlloc_2584_, 5, v_defEqPerm_2570_);
v___x_2576_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 1, v___x_2576_);
v___x_2578_ = v___x_2563_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_mctx_2558_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_zetaDeltaFVarIds_2559_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_postponed_2560_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v_diag_2561_);
v___x_2578_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_st_ref_put(v_a_2497_, v___x_2578_);
if (v_isShared_2555_ == 0)
{
v___x_2581_ = v___x_2554_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2551_);
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
v_resetjp_2591_:
{
lean_object* v_inferType_2594_; lean_object* v___x_2595_; 
v_inferType_2594_ = lean_ctor_get(v_cache_2590_, 0);
lean_inc_ref(v_inferType_2594_);
lean_dec_ref(v_cache_2590_);
lean_inc(v_a_2545_);
v___x_2595_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2542_, v___x_2543_, v_inferType_2594_, v_a_2545_);
lean_dec_ref(v_inferType_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; lean_object* v_toApplicative_2597_; lean_object* v_toFunctor_2598_; lean_object* v_toSeq_2599_; lean_object* v_toSeqLeft_2600_; lean_object* v_toSeqRight_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; lean_object* v___f_2608_; lean_object* v___f_2609_; lean_object* v___x_2611_; 
lean_del_object(v___x_2547_);
v___x_2596_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2597_ = lean_ctor_get(v___x_2596_, 0);
v_toFunctor_2598_ = lean_ctor_get(v_toApplicative_2597_, 0);
v_toSeq_2599_ = lean_ctor_get(v_toApplicative_2597_, 2);
v_toSeqLeft_2600_ = lean_ctor_get(v_toApplicative_2597_, 3);
v_toSeqRight_2601_ = lean_ctor_get(v_toApplicative_2597_, 4);
v___f_2602_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2603_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2598_, 2);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toFunctor_2598_);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2605_, 0, v_toFunctor_2598_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___f_2604_);
lean_ctor_set(v___x_2606_, 1, v___f_2605_);
lean_inc(v_toSeqRight_2601_);
v___f_2607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2607_, 0, v_toSeqRight_2601_);
lean_inc(v_toSeqLeft_2600_);
v___f_2608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2608_, 0, v_toSeqLeft_2600_);
lean_inc(v_toSeq_2599_);
v___f_2609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2609_, 0, v_toSeq_2599_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___f_2607_);
lean_ctor_set(v___x_2592_, 3, v___f_2608_);
lean_ctor_set(v___x_2592_, 2, v___f_2609_);
lean_ctor_set(v___x_2592_, 1, v___f_2602_);
lean_ctor_set(v___x_2592_, 0, v___x_2606_);
v___x_2611_ = v___x_2592_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v___f_2602_);
lean_ctor_set(v_reuseFailAlloc_2632_, 2, v___f_2609_);
lean_ctor_set(v_reuseFailAlloc_2632_, 3, v___f_2608_);
lean_ctor_set(v_reuseFailAlloc_2632_, 4, v___f_2607_);
v___x_2611_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_toCold_2618_; lean_object* v_cancelTk_x3f_2619_; 
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___f_2603_);
v___x_2613_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2614_ = l_Lean_Core_instMonadRefCoreM;
v___x_2615_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2616_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2615_, v___x_2612_);
v___x_2617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2613_);
lean_ctor_set(v___x_2617_, 1, v___x_2614_);
lean_ctor_set(v___x_2617_, 2, v___x_2616_);
v_toCold_2618_ = lean_ctor_get(v_a_2498_, 0);
v_cancelTk_x3f_2619_ = lean_ctor_get(v_toCold_2618_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2619_) == 1)
{
lean_object* v_val_2620_; uint8_t v___x_2621_; 
v_val_2620_ = lean_ctor_get(v_cancelTk_x3f_2619_, 0);
v___x_2621_ = l_IO_CancelToken_isSet(v_val_2620_);
if (v___x_2621_ == 0)
{
lean_dec_ref_known(v___x_2617_, 3);
goto v___jp_2549_;
}
else
{
lean_object* v___x_2058__overap_2622_; lean_object* v___x_2623_; 
v___x_2058__overap_2622_ = l_Lean_throwInterruptException___redArg(v___x_2617_);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
v___x_2623_ = lean_apply_3(v___x_2058__overap_2622_, v_a_2498_, v_a_2499_, lean_box(0));
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_dec_ref_known(v___x_2623_, 1);
goto v___jp_2549_;
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_inferType_2495_);
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2617_, 3);
goto v___jp_2549_;
}
}
}
else
{
lean_object* v_val_2633_; lean_object* v___x_2635_; 
lean_del_object(v___x_2592_);
lean_dec(v_a_2545_);
lean_dec_ref(v_inferType_2495_);
v_val_2633_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v___x_2595_, 1);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_val_2633_);
v___x_2635_ = v___x_2547_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_val_2633_);
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
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_inferType_2495_);
v_a_2643_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2544_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2544_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
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
lean_object* v___x_2031__overap_2528_; lean_object* v___x_2529_; 
v___x_2031__overap_2528_ = l_Lean_throwInterruptException___redArg(v___x_2522_);
lean_inc(v_a_2499_);
lean_inc_ref(v_a_2498_);
v___x_2529_ = lean_apply_3(v___x_2031__overap_2528_, v_a_2498_, v_a_2499_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2651_, lean_object* v_inferType_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2651_, v_inferType_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2711_; uint8_t v_beta_2712_; 
v___x_2711_ = l_Lean_Meta_Context_config(v___y_2660_);
v_beta_2712_ = lean_ctor_get_uint8(v___x_2711_, 13);
if (v_beta_2712_ == 0)
{
lean_dec_ref(v___x_2711_);
goto v___jp_2665_;
}
else
{
uint8_t v_iota_2713_; 
v_iota_2713_ = lean_ctor_get_uint8(v___x_2711_, 12);
if (v_iota_2713_ == 0)
{
lean_dec_ref(v___x_2711_);
goto v___jp_2665_;
}
else
{
uint8_t v_zeta_2714_; 
v_zeta_2714_ = lean_ctor_get_uint8(v___x_2711_, 15);
if (v_zeta_2714_ == 0)
{
lean_dec_ref(v___x_2711_);
goto v___jp_2665_;
}
else
{
uint8_t v_zetaHave_2715_; 
v_zetaHave_2715_ = lean_ctor_get_uint8(v___x_2711_, 18);
if (v_zetaHave_2715_ == 0)
{
lean_dec_ref(v___x_2711_);
goto v___jp_2665_;
}
else
{
uint8_t v_zetaDelta_2716_; 
v_zetaDelta_2716_ = lean_ctor_get_uint8(v___x_2711_, 16);
if (v_zetaDelta_2716_ == 0)
{
lean_dec_ref(v___x_2711_);
goto v___jp_2665_;
}
else
{
uint8_t v_etaStruct_2717_; uint8_t v_proj_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_etaStruct_2717_ = lean_ctor_get_uint8(v___x_2711_, 10);
v_proj_2718_ = lean_ctor_get_uint8(v___x_2711_, 14);
lean_dec_ref(v___x_2711_);
v___x_2719_ = lean_box(v_proj_2718_);
v___x_2720_ = lean_obj_tag_nat(v___x_2719_);
lean_dec(v___x_2719_);
v___x_2721_ = lean_unsigned_to_nat(2u);
v___x_2722_ = lean_nat_dec_eq(v___x_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
goto v___jp_2665_;
}
else
{
uint8_t v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = 0;
v___x_2724_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2717_, v___x_2723_);
if (v___x_2724_ == 0)
{
goto v___jp_2665_;
}
else
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_apply_5(v_x_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, lean_box(0));
return v___x_2725_;
}
}
}
}
}
}
}
v___jp_2665_:
{
lean_object* v___x_2666_; uint8_t v_foApprox_2667_; uint8_t v_ctxApprox_2668_; uint8_t v_quasiPatternApprox_2669_; uint8_t v_constApprox_2670_; uint8_t v_isDefEqStuckEx_2671_; uint8_t v_unificationHints_2672_; uint8_t v_proofIrrelevance_2673_; uint8_t v_assignSyntheticOpaque_2674_; uint8_t v_offsetCnstrs_2675_; uint8_t v_transparency_2676_; uint8_t v_univApprox_2677_; uint8_t v_zetaUnused_2678_; uint8_t v_canUnfoldPredicateConfig_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2710_; 
v___x_2666_ = l_Lean_Meta_Context_config(v___y_2660_);
v_foApprox_2667_ = lean_ctor_get_uint8(v___x_2666_, 0);
v_ctxApprox_2668_ = lean_ctor_get_uint8(v___x_2666_, 1);
v_quasiPatternApprox_2669_ = lean_ctor_get_uint8(v___x_2666_, 2);
v_constApprox_2670_ = lean_ctor_get_uint8(v___x_2666_, 3);
v_isDefEqStuckEx_2671_ = lean_ctor_get_uint8(v___x_2666_, 4);
v_unificationHints_2672_ = lean_ctor_get_uint8(v___x_2666_, 5);
v_proofIrrelevance_2673_ = lean_ctor_get_uint8(v___x_2666_, 6);
v_assignSyntheticOpaque_2674_ = lean_ctor_get_uint8(v___x_2666_, 7);
v_offsetCnstrs_2675_ = lean_ctor_get_uint8(v___x_2666_, 8);
v_transparency_2676_ = lean_ctor_get_uint8(v___x_2666_, 9);
v_univApprox_2677_ = lean_ctor_get_uint8(v___x_2666_, 11);
v_zetaUnused_2678_ = lean_ctor_get_uint8(v___x_2666_, 17);
v_canUnfoldPredicateConfig_2679_ = lean_ctor_get_uint8(v___x_2666_, 19);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2681_ = v___x_2666_;
v_isShared_2682_ = v_isSharedCheck_2710_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v___x_2666_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2710_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
uint8_t v___x_2683_; uint8_t v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2687_; 
v___x_2683_ = 1;
v___x_2684_ = 0;
v___x_2685_ = 2;
if (v_isShared_2682_ == 0)
{
v___x_2687_ = v___x_2681_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 0, v_foApprox_2667_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 1, v_ctxApprox_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 2, v_quasiPatternApprox_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 3, v_constApprox_2670_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 4, v_isDefEqStuckEx_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 5, v_unificationHints_2672_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 6, v_proofIrrelevance_2673_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 7, v_assignSyntheticOpaque_2674_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 8, v_offsetCnstrs_2675_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 9, v_transparency_2676_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 11, v_univApprox_2677_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 17, v_zetaUnused_2678_);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 19, v_canUnfoldPredicateConfig_2679_);
v___x_2687_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
uint8_t v_trackZetaDelta_2688_; lean_object* v_zetaDeltaSet_2689_; lean_object* v_lctx_2690_; lean_object* v_localInstances_2691_; lean_object* v_defEqCtx_x3f_2692_; lean_object* v_synthPendingDepth_2693_; lean_object* v_customCanUnfoldPredicate_x3f_2694_; uint8_t v_univApprox_2695_; uint8_t v_inTypeClassResolution_2696_; uint8_t v_cacheInferType_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2707_; 
lean_ctor_set_uint8(v___x_2687_, 10, v___x_2684_);
lean_ctor_set_uint8(v___x_2687_, 12, v___x_2683_);
lean_ctor_set_uint8(v___x_2687_, 13, v___x_2683_);
lean_ctor_set_uint8(v___x_2687_, 14, v___x_2685_);
lean_ctor_set_uint8(v___x_2687_, 15, v___x_2683_);
lean_ctor_set_uint8(v___x_2687_, 16, v___x_2683_);
lean_ctor_set_uint8(v___x_2687_, 18, v___x_2683_);
v_trackZetaDelta_2688_ = lean_ctor_get_uint8(v___y_2660_, sizeof(void*)*7);
v_zetaDeltaSet_2689_ = lean_ctor_get(v___y_2660_, 1);
v_lctx_2690_ = lean_ctor_get(v___y_2660_, 2);
v_localInstances_2691_ = lean_ctor_get(v___y_2660_, 3);
v_defEqCtx_x3f_2692_ = lean_ctor_get(v___y_2660_, 4);
v_synthPendingDepth_2693_ = lean_ctor_get(v___y_2660_, 5);
v_customCanUnfoldPredicate_x3f_2694_ = lean_ctor_get(v___y_2660_, 6);
v_univApprox_2695_ = lean_ctor_get_uint8(v___y_2660_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2696_ = lean_ctor_get_uint8(v___y_2660_, sizeof(void*)*7 + 2);
v_cacheInferType_2697_ = lean_ctor_get_uint8(v___y_2660_, sizeof(void*)*7 + 3);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___y_2660_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v___y_2660_, 0);
lean_dec(v_unused_2708_);
v___x_2699_ = v___y_2660_;
v_isShared_2700_ = v_isSharedCheck_2707_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2694_);
lean_inc(v_synthPendingDepth_2693_);
lean_inc(v_defEqCtx_x3f_2692_);
lean_inc(v_localInstances_2691_);
lean_inc(v_lctx_2690_);
lean_inc(v_zetaDeltaSet_2689_);
lean_dec(v___y_2660_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2707_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
uint64_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2701_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2687_);
v___x_2702_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2702_, 0, v___x_2687_);
lean_ctor_set_uint64(v___x_2702_, sizeof(void*)*1, v___x_2701_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2702_);
v___x_2704_ = v___x_2699_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_zetaDeltaSet_2689_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_lctx_2690_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_localInstances_2691_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_defEqCtx_x3f_2692_);
lean_ctor_set(v_reuseFailAlloc_2706_, 5, v_synthPendingDepth_2693_);
lean_ctor_set(v_reuseFailAlloc_2706_, 6, v_customCanUnfoldPredicate_x3f_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*7, v_trackZetaDelta_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*7 + 1, v_univApprox_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, sizeof(void*)*7 + 3, v_cacheInferType_2697_);
v___x_2704_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_apply_5(v_x_2659_, v___x_2704_, v___y_2661_, v___y_2662_, v___y_2663_, lean_box(0));
return v___x_2705_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___y_2740_; lean_object* v___x_2757_; uint8_t v_transparency_2758_; uint8_t v___x_2759_; uint8_t v___x_2760_; 
v___x_2757_ = l_Lean_Meta_Context_config(v_a_2734_);
v_transparency_2758_ = lean_ctor_get_uint8(v___x_2757_, 9);
lean_dec_ref(v___x_2757_);
v___x_2759_ = 1;
v___x_2760_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2758_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
lean_inc(v_a_2737_);
lean_inc_ref(v_a_2736_);
lean_inc(v_a_2735_);
lean_inc_ref(v_a_2734_);
v___x_2761_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
v___y_2740_ = v___x_2761_;
goto v___jp_2739_;
}
else
{
lean_object* v_keyedConfig_2762_; uint8_t v_trackZetaDelta_2763_; lean_object* v_zetaDeltaSet_2764_; lean_object* v_lctx_2765_; lean_object* v_localInstances_2766_; lean_object* v_defEqCtx_x3f_2767_; lean_object* v_synthPendingDepth_2768_; lean_object* v_customCanUnfoldPredicate_x3f_2769_; uint8_t v_univApprox_2770_; uint8_t v_inTypeClassResolution_2771_; uint8_t v_cacheInferType_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_keyedConfig_2762_ = lean_ctor_get(v_a_2734_, 0);
v_trackZetaDelta_2763_ = lean_ctor_get_uint8(v_a_2734_, sizeof(void*)*7);
v_zetaDeltaSet_2764_ = lean_ctor_get(v_a_2734_, 1);
v_lctx_2765_ = lean_ctor_get(v_a_2734_, 2);
v_localInstances_2766_ = lean_ctor_get(v_a_2734_, 3);
v_defEqCtx_x3f_2767_ = lean_ctor_get(v_a_2734_, 4);
v_synthPendingDepth_2768_ = lean_ctor_get(v_a_2734_, 5);
v_customCanUnfoldPredicate_x3f_2769_ = lean_ctor_get(v_a_2734_, 6);
v_univApprox_2770_ = lean_ctor_get_uint8(v_a_2734_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2771_ = lean_ctor_get_uint8(v_a_2734_, sizeof(void*)*7 + 2);
v_cacheInferType_2772_ = lean_ctor_get_uint8(v_a_2734_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2762_);
v___x_2773_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2759_, v_keyedConfig_2762_);
lean_inc(v_customCanUnfoldPredicate_x3f_2769_);
lean_inc(v_synthPendingDepth_2768_);
lean_inc(v_defEqCtx_x3f_2767_);
lean_inc_ref(v_localInstances_2766_);
lean_inc_ref(v_lctx_2765_);
lean_inc(v_zetaDeltaSet_2764_);
v___x_2774_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v_zetaDeltaSet_2764_);
lean_ctor_set(v___x_2774_, 2, v_lctx_2765_);
lean_ctor_set(v___x_2774_, 3, v_localInstances_2766_);
lean_ctor_set(v___x_2774_, 4, v_defEqCtx_x3f_2767_);
lean_ctor_set(v___x_2774_, 5, v_synthPendingDepth_2768_);
lean_ctor_set(v___x_2774_, 6, v_customCanUnfoldPredicate_x3f_2769_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7, v_trackZetaDelta_2763_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7 + 1, v_univApprox_2770_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2771_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7 + 3, v_cacheInferType_2772_);
lean_inc(v_a_2737_);
lean_inc_ref(v_a_2736_);
lean_inc(v_a_2735_);
v___x_2775_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2733_, v___x_2774_, v_a_2735_, v_a_2736_, v_a_2737_);
v___y_2740_ = v___x_2775_;
goto v___jp_2739_;
}
v___jp_2739_:
{
if (lean_obj_tag(v___y_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
v_a_2741_ = lean_ctor_get(v___y_2740_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___y_2740_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___y_2740_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___y_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_a_2749_ = lean_ctor_get(v___y_2740_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___y_2740_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___y_2740_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___y_2740_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2783_, lean_object* v_x_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___y_2791_; lean_object* v___x_2808_; uint8_t v_transparency_2809_; uint8_t v___x_2810_; uint8_t v___x_2811_; 
v___x_2808_ = l_Lean_Meta_Context_config(v_a_2785_);
v_transparency_2809_ = lean_ctor_get_uint8(v___x_2808_, 9);
lean_dec_ref(v___x_2808_);
v___x_2810_ = 1;
v___x_2811_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
lean_inc(v_a_2788_);
lean_inc_ref(v_a_2787_);
lean_inc(v_a_2786_);
lean_inc_ref(v_a_2785_);
v___x_2812_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
v___y_2791_ = v___x_2812_;
goto v___jp_2790_;
}
else
{
lean_object* v_keyedConfig_2813_; uint8_t v_trackZetaDelta_2814_; lean_object* v_zetaDeltaSet_2815_; lean_object* v_lctx_2816_; lean_object* v_localInstances_2817_; lean_object* v_defEqCtx_x3f_2818_; lean_object* v_synthPendingDepth_2819_; lean_object* v_customCanUnfoldPredicate_x3f_2820_; uint8_t v_univApprox_2821_; uint8_t v_inTypeClassResolution_2822_; uint8_t v_cacheInferType_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_keyedConfig_2813_ = lean_ctor_get(v_a_2785_, 0);
v_trackZetaDelta_2814_ = lean_ctor_get_uint8(v_a_2785_, sizeof(void*)*7);
v_zetaDeltaSet_2815_ = lean_ctor_get(v_a_2785_, 1);
v_lctx_2816_ = lean_ctor_get(v_a_2785_, 2);
v_localInstances_2817_ = lean_ctor_get(v_a_2785_, 3);
v_defEqCtx_x3f_2818_ = lean_ctor_get(v_a_2785_, 4);
v_synthPendingDepth_2819_ = lean_ctor_get(v_a_2785_, 5);
v_customCanUnfoldPredicate_x3f_2820_ = lean_ctor_get(v_a_2785_, 6);
v_univApprox_2821_ = lean_ctor_get_uint8(v_a_2785_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2822_ = lean_ctor_get_uint8(v_a_2785_, sizeof(void*)*7 + 2);
v_cacheInferType_2823_ = lean_ctor_get_uint8(v_a_2785_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2813_);
v___x_2824_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2810_, v_keyedConfig_2813_);
lean_inc(v_customCanUnfoldPredicate_x3f_2820_);
lean_inc(v_synthPendingDepth_2819_);
lean_inc(v_defEqCtx_x3f_2818_);
lean_inc_ref(v_localInstances_2817_);
lean_inc_ref(v_lctx_2816_);
lean_inc(v_zetaDeltaSet_2815_);
v___x_2825_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
lean_ctor_set(v___x_2825_, 1, v_zetaDeltaSet_2815_);
lean_ctor_set(v___x_2825_, 2, v_lctx_2816_);
lean_ctor_set(v___x_2825_, 3, v_localInstances_2817_);
lean_ctor_set(v___x_2825_, 4, v_defEqCtx_x3f_2818_);
lean_ctor_set(v___x_2825_, 5, v_synthPendingDepth_2819_);
lean_ctor_set(v___x_2825_, 6, v_customCanUnfoldPredicate_x3f_2820_);
lean_ctor_set_uint8(v___x_2825_, sizeof(void*)*7, v_trackZetaDelta_2814_);
lean_ctor_set_uint8(v___x_2825_, sizeof(void*)*7 + 1, v_univApprox_2821_);
lean_ctor_set_uint8(v___x_2825_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2822_);
lean_ctor_set_uint8(v___x_2825_, sizeof(void*)*7 + 3, v_cacheInferType_2823_);
lean_inc(v_a_2788_);
lean_inc_ref(v_a_2787_);
lean_inc(v_a_2786_);
v___x_2826_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2784_, v___x_2825_, v_a_2786_, v_a_2787_, v_a_2788_);
v___y_2791_ = v___x_2826_;
goto v___jp_2790_;
}
v___jp_2790_:
{
if (lean_obj_tag(v___y_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___y_2791_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___y_2791_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___y_2791_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___y_2791_);
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
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v___y_2791_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___y_2791_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___y_2791_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___y_2791_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2827_, lean_object* v_x_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2827_, v_x_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
return v_res_2834_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = lean_box(0);
v___x_2836_ = l_Lean_interruptExceptionId;
v___x_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v___x_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2853_, lean_object* v_x_2854_, lean_object* v_x_2855_, lean_object* v_x_2856_){
_start:
{
lean_object* v_ks_2857_; lean_object* v_vs_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2887_; 
v_ks_2857_ = lean_ctor_get(v_x_2853_, 0);
v_vs_2858_ = lean_ctor_get(v_x_2853_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2853_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2860_ = v_x_2853_;
v_isShared_2861_ = v_isSharedCheck_2887_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_vs_2858_);
lean_inc(v_ks_2857_);
lean_dec(v_x_2853_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2887_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
uint8_t v___y_2863_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = lean_array_get_size(v_ks_2857_);
v___x_2876_ = lean_nat_dec_lt(v_x_2854_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_del_object(v___x_2860_);
lean_dec(v_x_2854_);
v___x_2877_ = lean_array_push(v_ks_2857_, v_x_2855_);
v___x_2878_ = lean_array_push(v_vs_2858_, v_x_2856_);
v___x_2879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v_expr_2880_; uint64_t v_configKey_2881_; lean_object* v_k_x27_2882_; lean_object* v_expr_2883_; uint64_t v_configKey_2884_; uint8_t v___x_2885_; 
v_expr_2880_ = lean_ctor_get(v_x_2855_, 0);
v_configKey_2881_ = lean_ctor_get_uint64(v_x_2855_, sizeof(void*)*1);
v_k_x27_2882_ = lean_array_fget_borrowed(v_ks_2857_, v_x_2854_);
v_expr_2883_ = lean_ctor_get(v_k_x27_2882_, 0);
v_configKey_2884_ = lean_ctor_get_uint64(v_k_x27_2882_, sizeof(void*)*1);
v___x_2885_ = lean_expr_equal(v_expr_2880_, v_expr_2883_);
if (v___x_2885_ == 0)
{
v___y_2863_ = v___x_2885_;
goto v___jp_2862_;
}
else
{
uint8_t v___x_2886_; 
v___x_2886_ = lean_uint64_dec_eq(v_configKey_2881_, v_configKey_2884_);
v___y_2863_ = v___x_2886_;
goto v___jp_2862_;
}
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
lean_object* v___x_2865_; 
if (v_isShared_2861_ == 0)
{
v___x_2865_ = v___x_2860_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_ks_2857_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_vs_2858_);
v___x_2865_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_unsigned_to_nat(1u);
v___x_2867_ = lean_nat_add(v_x_2854_, v___x_2866_);
lean_dec(v_x_2854_);
v_x_2853_ = v___x_2865_;
v_x_2854_ = v___x_2867_;
goto _start;
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2870_ = lean_array_fset(v_ks_2857_, v_x_2854_, v_x_2855_);
v___x_2871_ = lean_array_fset(v_vs_2858_, v_x_2854_, v_x_2856_);
lean_dec(v_x_2854_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2871_);
lean_ctor_set(v___x_2860_, 0, v___x_2870_);
v___x_2873_ = v___x_2860_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2888_, lean_object* v_k_2889_, lean_object* v_v_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_unsigned_to_nat(0u);
v___x_2892_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2888_, v___x_2891_, v_k_2889_, v_v_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2893_, size_t v_x_2894_, size_t v_x_2895_, lean_object* v_x_2896_, lean_object* v_x_2897_){
_start:
{
if (lean_obj_tag(v_x_2893_) == 0)
{
lean_object* v_es_2898_; size_t v___x_2899_; size_t v___x_2900_; lean_object* v_j_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v_es_2898_ = lean_ctor_get(v_x_2893_, 0);
v___x_2899_ = ((size_t)31ULL);
v___x_2900_ = lean_usize_land(v_x_2894_, v___x_2899_);
v_j_2901_ = lean_usize_to_nat(v___x_2900_);
v___x_2902_ = lean_array_get_size(v_es_2898_);
v___x_2903_ = lean_nat_dec_lt(v_j_2901_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_dec(v_j_2901_);
lean_dec(v_x_2897_);
lean_dec_ref(v_x_2896_);
return v_x_2893_;
}
else
{
lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2949_; 
lean_inc_ref(v_es_2898_);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_x_2893_);
if (v_isSharedCheck_2949_ == 0)
{
lean_object* v_unused_2950_; 
v_unused_2950_ = lean_ctor_get(v_x_2893_, 0);
lean_dec(v_unused_2950_);
v___x_2905_ = v_x_2893_;
v_isShared_2906_ = v_isSharedCheck_2949_;
goto v_resetjp_2904_;
}
else
{
lean_dec(v_x_2893_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2949_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_v_2907_; lean_object* v___x_2908_; lean_object* v_xs_x27_2909_; lean_object* v___y_2911_; 
v_v_2907_ = lean_array_fget(v_es_2898_, v_j_2901_);
v___x_2908_ = lean_box(0);
v_xs_x27_2909_ = lean_array_fset(v_es_2898_, v_j_2901_, v___x_2908_);
switch(lean_obj_tag(v_v_2907_))
{
case 0:
{
lean_object* v_key_2916_; lean_object* v_val_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2934_; 
v_key_2916_ = lean_ctor_get(v_v_2907_, 0);
v_val_2917_ = lean_ctor_get(v_v_2907_, 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_v_2907_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2919_ = v_v_2907_;
v_isShared_2920_ = v_isSharedCheck_2934_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_val_2917_);
lean_inc(v_key_2916_);
lean_dec(v_v_2907_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2934_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
uint8_t v___y_2922_; lean_object* v_expr_2928_; uint64_t v_configKey_2929_; lean_object* v_expr_2930_; uint64_t v_configKey_2931_; uint8_t v___x_2932_; 
v_expr_2928_ = lean_ctor_get(v_x_2896_, 0);
v_configKey_2929_ = lean_ctor_get_uint64(v_x_2896_, sizeof(void*)*1);
v_expr_2930_ = lean_ctor_get(v_key_2916_, 0);
v_configKey_2931_ = lean_ctor_get_uint64(v_key_2916_, sizeof(void*)*1);
v___x_2932_ = lean_expr_equal(v_expr_2928_, v_expr_2930_);
if (v___x_2932_ == 0)
{
v___y_2922_ = v___x_2932_;
goto v___jp_2921_;
}
else
{
uint8_t v___x_2933_; 
v___x_2933_ = lean_uint64_dec_eq(v_configKey_2929_, v_configKey_2931_);
v___y_2922_ = v___x_2933_;
goto v___jp_2921_;
}
v___jp_2921_:
{
if (v___y_2922_ == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_del_object(v___x_2919_);
v___x_2923_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2916_, v_val_2917_, v_x_2896_, v_x_2897_);
v___x_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
v___y_2911_ = v___x_2924_;
goto v___jp_2910_;
}
else
{
lean_object* v___x_2926_; 
lean_dec(v_val_2917_);
lean_dec(v_key_2916_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v_x_2897_);
lean_ctor_set(v___x_2919_, 0, v_x_2896_);
v___x_2926_ = v___x_2919_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_x_2896_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_x_2897_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
v___y_2911_ = v___x_2926_;
goto v___jp_2910_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2947_; 
v_node_2935_ = lean_ctor_get(v_v_2907_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_v_2907_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2937_ = v_v_2907_;
v_isShared_2938_ = v_isSharedCheck_2947_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_node_2935_);
lean_dec(v_v_2907_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2947_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
size_t v___x_2939_; size_t v___x_2940_; size_t v___x_2941_; size_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2939_ = ((size_t)5ULL);
v___x_2940_ = lean_usize_shift_right(v_x_2894_, v___x_2939_);
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_add(v_x_2895_, v___x_2941_);
v___x_2943_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2935_, v___x_2940_, v___x_2942_, v_x_2896_, v_x_2897_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 0, v___x_2943_);
v___x_2945_ = v___x_2937_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
v___y_2911_ = v___x_2945_;
goto v___jp_2910_;
}
}
}
default: 
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_x_2896_);
lean_ctor_set(v___x_2948_, 1, v_x_2897_);
v___y_2911_ = v___x_2948_;
goto v___jp_2910_;
}
}
v___jp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = lean_array_fset(v_xs_x27_2909_, v_j_2901_, v___y_2911_);
lean_dec(v_j_2901_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2912_);
v___x_2914_ = v___x_2905_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
else
{
lean_object* v_ks_2951_; lean_object* v_vs_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2970_; 
v_ks_2951_ = lean_ctor_get(v_x_2893_, 0);
v_vs_2952_ = lean_ctor_get(v_x_2893_, 1);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2893_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2954_ = v_x_2893_;
v_isShared_2955_ = v_isSharedCheck_2970_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_vs_2952_);
lean_inc(v_ks_2951_);
lean_dec(v_x_2893_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2970_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_ks_2951_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_vs_2952_);
v___x_2957_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v_newNode_2958_; size_t v___x_2959_; uint8_t v___x_2960_; 
v_newNode_2958_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2957_, v_x_2896_, v_x_2897_);
v___x_2959_ = ((size_t)7ULL);
v___x_2960_ = lean_usize_dec_le(v___x_2959_, v_x_2895_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2958_);
v___x_2962_ = lean_unsigned_to_nat(4u);
v___x_2963_ = lean_nat_dec_lt(v___x_2961_, v___x_2962_);
lean_dec(v___x_2961_);
if (v___x_2963_ == 0)
{
lean_object* v_ks_2964_; lean_object* v_vs_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_ks_2964_ = lean_ctor_get(v_newNode_2958_, 0);
lean_inc_ref(v_ks_2964_);
v_vs_2965_ = lean_ctor_get(v_newNode_2958_, 1);
lean_inc_ref(v_vs_2965_);
lean_dec_ref(v_newNode_2958_);
v___x_2966_ = lean_unsigned_to_nat(0u);
v___x_2967_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2968_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2895_, v_ks_2964_, v_vs_2965_, v___x_2966_, v___x_2967_);
lean_dec_ref(v_vs_2965_);
lean_dec_ref(v_ks_2964_);
return v___x_2968_;
}
else
{
return v_newNode_2958_;
}
}
else
{
return v_newNode_2958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2971_, lean_object* v_keys_2972_, lean_object* v_vals_2973_, lean_object* v_i_2974_, lean_object* v_entries_2975_){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = lean_array_get_size(v_keys_2972_);
v___x_2977_ = lean_nat_dec_lt(v_i_2974_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_dec(v_i_2974_);
return v_entries_2975_;
}
else
{
lean_object* v_k_2978_; lean_object* v_expr_2979_; uint64_t v_configKey_2980_; lean_object* v_v_2981_; uint64_t v___x_2982_; uint64_t v___x_2983_; size_t v_h_2984_; size_t v___x_2985_; lean_object* v___x_2986_; size_t v___x_2987_; size_t v___x_2988_; size_t v___x_2989_; size_t v_h_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_k_2978_ = lean_array_fget_borrowed(v_keys_2972_, v_i_2974_);
v_expr_2979_ = lean_ctor_get(v_k_2978_, 0);
v_configKey_2980_ = lean_ctor_get_uint64(v_k_2978_, sizeof(void*)*1);
v_v_2981_ = lean_array_fget_borrowed(v_vals_2973_, v_i_2974_);
v___x_2982_ = l_Lean_Expr_hash(v_expr_2979_);
v___x_2983_ = lean_uint64_mix_hash(v___x_2982_, v_configKey_2980_);
v_h_2984_ = lean_uint64_to_usize(v___x_2983_);
v___x_2985_ = ((size_t)5ULL);
v___x_2986_ = lean_unsigned_to_nat(1u);
v___x_2987_ = ((size_t)1ULL);
v___x_2988_ = lean_usize_sub(v_depth_2971_, v___x_2987_);
v___x_2989_ = lean_usize_mul(v___x_2985_, v___x_2988_);
v_h_2990_ = lean_usize_shift_right(v_h_2984_, v___x_2989_);
v___x_2991_ = lean_nat_add(v_i_2974_, v___x_2986_);
lean_dec(v_i_2974_);
lean_inc(v_v_2981_);
lean_inc(v_k_2978_);
v___x_2992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2975_, v_h_2990_, v_depth_2971_, v_k_2978_, v_v_2981_);
v_i_2974_ = v___x_2991_;
v_entries_2975_ = v___x_2992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2994_, lean_object* v_keys_2995_, lean_object* v_vals_2996_, lean_object* v_i_2997_, lean_object* v_entries_2998_){
_start:
{
size_t v_depth_boxed_2999_; lean_object* v_res_3000_; 
v_depth_boxed_2999_ = lean_unbox_usize(v_depth_2994_);
lean_dec(v_depth_2994_);
v_res_3000_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2999_, v_keys_2995_, v_vals_2996_, v_i_2997_, v_entries_2998_);
lean_dec_ref(v_vals_2996_);
lean_dec_ref(v_keys_2995_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3001_, lean_object* v_x_3002_, lean_object* v_x_3003_, lean_object* v_x_3004_, lean_object* v_x_3005_){
_start:
{
size_t v_x_2395__boxed_3006_; size_t v_x_2396__boxed_3007_; lean_object* v_res_3008_; 
v_x_2395__boxed_3006_ = lean_unbox_usize(v_x_3002_);
lean_dec(v_x_3002_);
v_x_2396__boxed_3007_ = lean_unbox_usize(v_x_3003_);
lean_dec(v_x_3003_);
v_res_3008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3001_, v_x_2395__boxed_3006_, v_x_2396__boxed_3007_, v_x_3004_, v_x_3005_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3009_, lean_object* v_x_3010_, lean_object* v_x_3011_){
_start:
{
lean_object* v_expr_3012_; uint64_t v_configKey_3013_; uint64_t v___x_3014_; uint64_t v___x_3015_; size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; 
v_expr_3012_ = lean_ctor_get(v_x_3010_, 0);
v_configKey_3013_ = lean_ctor_get_uint64(v_x_3010_, sizeof(void*)*1);
v___x_3014_ = l_Lean_Expr_hash(v_expr_3012_);
v___x_3015_ = lean_uint64_mix_hash(v___x_3014_, v_configKey_3013_);
v___x_3016_ = lean_uint64_to_usize(v___x_3015_);
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3009_, v___x_3016_, v___x_3017_, v_x_3010_, v_x_3011_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3019_, lean_object* v_vals_3020_, lean_object* v_i_3021_, lean_object* v_k_3022_){
_start:
{
uint8_t v___y_3024_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = lean_array_get_size(v_keys_3019_);
v___x_3031_ = lean_nat_dec_lt(v_i_3021_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
lean_dec(v_i_3021_);
v___x_3032_ = lean_box(0);
return v___x_3032_;
}
else
{
lean_object* v_expr_3033_; uint64_t v_configKey_3034_; lean_object* v_k_x27_3035_; lean_object* v_expr_3036_; uint64_t v_configKey_3037_; uint8_t v___x_3038_; 
v_expr_3033_ = lean_ctor_get(v_k_3022_, 0);
v_configKey_3034_ = lean_ctor_get_uint64(v_k_3022_, sizeof(void*)*1);
v_k_x27_3035_ = lean_array_fget_borrowed(v_keys_3019_, v_i_3021_);
v_expr_3036_ = lean_ctor_get(v_k_x27_3035_, 0);
v_configKey_3037_ = lean_ctor_get_uint64(v_k_x27_3035_, sizeof(void*)*1);
v___x_3038_ = lean_expr_equal(v_expr_3033_, v_expr_3036_);
if (v___x_3038_ == 0)
{
v___y_3024_ = v___x_3038_;
goto v___jp_3023_;
}
else
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_uint64_dec_eq(v_configKey_3034_, v_configKey_3037_);
v___y_3024_ = v___x_3039_;
goto v___jp_3023_;
}
}
v___jp_3023_:
{
if (v___y_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_unsigned_to_nat(1u);
v___x_3026_ = lean_nat_add(v_i_3021_, v___x_3025_);
lean_dec(v_i_3021_);
v_i_3021_ = v___x_3026_;
goto _start;
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_array_fget_borrowed(v_vals_3020_, v_i_3021_);
lean_dec(v_i_3021_);
lean_inc(v___x_3028_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3040_, lean_object* v_vals_3041_, lean_object* v_i_3042_, lean_object* v_k_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3040_, v_vals_3041_, v_i_3042_, v_k_3043_);
lean_dec_ref(v_k_3043_);
lean_dec_ref(v_vals_3041_);
lean_dec_ref(v_keys_3040_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3045_, size_t v_x_3046_, lean_object* v_x_3047_){
_start:
{
if (lean_obj_tag(v_x_3045_) == 0)
{
lean_object* v_es_3048_; lean_object* v___x_3049_; size_t v___x_3050_; size_t v___x_3051_; lean_object* v_j_3052_; lean_object* v___x_3053_; 
v_es_3048_ = lean_ctor_get(v_x_3045_, 0);
v___x_3049_ = lean_box(2);
v___x_3050_ = ((size_t)31ULL);
v___x_3051_ = lean_usize_land(v_x_3046_, v___x_3050_);
v_j_3052_ = lean_usize_to_nat(v___x_3051_);
v___x_3053_ = lean_array_get_borrowed(v___x_3049_, v_es_3048_, v_j_3052_);
lean_dec(v_j_3052_);
switch(lean_obj_tag(v___x_3053_))
{
case 0:
{
lean_object* v_key_3054_; lean_object* v_val_3055_; uint8_t v___y_3057_; lean_object* v_expr_3060_; uint64_t v_configKey_3061_; lean_object* v_expr_3062_; uint64_t v_configKey_3063_; uint8_t v___x_3064_; 
v_key_3054_ = lean_ctor_get(v___x_3053_, 0);
v_val_3055_ = lean_ctor_get(v___x_3053_, 1);
v_expr_3060_ = lean_ctor_get(v_x_3047_, 0);
v_configKey_3061_ = lean_ctor_get_uint64(v_x_3047_, sizeof(void*)*1);
v_expr_3062_ = lean_ctor_get(v_key_3054_, 0);
v_configKey_3063_ = lean_ctor_get_uint64(v_key_3054_, sizeof(void*)*1);
v___x_3064_ = lean_expr_equal(v_expr_3060_, v_expr_3062_);
if (v___x_3064_ == 0)
{
v___y_3057_ = v___x_3064_;
goto v___jp_3056_;
}
else
{
uint8_t v___x_3065_; 
v___x_3065_ = lean_uint64_dec_eq(v_configKey_3061_, v_configKey_3063_);
v___y_3057_ = v___x_3065_;
goto v___jp_3056_;
}
v___jp_3056_:
{
if (v___y_3057_ == 0)
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_box(0);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; 
lean_inc(v_val_3055_);
v___x_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_val_3055_);
return v___x_3059_;
}
}
}
case 1:
{
lean_object* v_node_3066_; size_t v___x_3067_; size_t v___x_3068_; 
v_node_3066_ = lean_ctor_get(v___x_3053_, 0);
v___x_3067_ = ((size_t)5ULL);
v___x_3068_ = lean_usize_shift_right(v_x_3046_, v___x_3067_);
v_x_3045_ = v_node_3066_;
v_x_3046_ = v___x_3068_;
goto _start;
}
default: 
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_box(0);
return v___x_3070_;
}
}
}
else
{
lean_object* v_ks_3071_; lean_object* v_vs_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_ks_3071_ = lean_ctor_get(v_x_3045_, 0);
v_vs_3072_ = lean_ctor_get(v_x_3045_, 1);
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3071_, v_vs_3072_, v___x_3073_, v_x_3047_);
return v___x_3074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_){
_start:
{
size_t v_x_2599__boxed_3078_; lean_object* v_res_3079_; 
v_x_2599__boxed_3078_ = lean_unbox_usize(v_x_3076_);
lean_dec(v_x_3076_);
v_res_3079_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3075_, v_x_2599__boxed_3078_, v_x_3077_);
lean_dec_ref(v_x_3077_);
lean_dec_ref(v_x_3075_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
lean_object* v_expr_3082_; uint64_t v_configKey_3083_; uint64_t v___x_3084_; uint64_t v___x_3085_; size_t v___x_3086_; lean_object* v___x_3087_; 
v_expr_3082_ = lean_ctor_get(v_x_3081_, 0);
v_configKey_3083_ = lean_ctor_get_uint64(v_x_3081_, sizeof(void*)*1);
v___x_3084_ = l_Lean_Expr_hash(v_expr_3082_);
v___x_3085_ = lean_uint64_mix_hash(v___x_3084_, v_configKey_3083_);
v___x_3086_ = lean_uint64_to_usize(v___x_3085_);
v___x_3087_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3080_, v___x_3086_, v_x_3081_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3088_, lean_object* v_x_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3088_, v_x_3089_);
lean_dec_ref(v_x_3089_);
lean_dec_ref(v_x_3088_);
return v_res_3090_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3093_ = l_Lean_stringToMessageData(v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
switch(lean_obj_tag(v_e_3094_))
{
case 0:
{
lean_object* v_deBruijnIndex_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_deBruijnIndex_3132_ = lean_ctor_get(v_e_3094_, 0);
lean_inc(v_deBruijnIndex_3132_);
lean_dec_ref_known(v_e_3094_, 1);
v___x_3133_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3134_ = l_Lean_mkBVar(v_deBruijnIndex_3132_);
v___x_3135_ = l_Lean_MessageData_ofExpr(v___x_3134_);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3133_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3136_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3137_;
}
case 1:
{
lean_object* v_fvarId_3138_; lean_object* v___x_3139_; 
v_fvarId_3138_ = lean_ctor_get(v_e_3094_, 0);
lean_inc(v_fvarId_3138_);
lean_dec_ref_known(v_e_3094_, 1);
v___x_3139_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3138_, v_a_3095_, v_a_3097_, v_a_3098_);
return v___x_3139_;
}
case 2:
{
lean_object* v_mvarId_3140_; lean_object* v___x_3141_; 
v_mvarId_3140_ = lean_ctor_get(v_e_3094_, 0);
lean_inc(v_mvarId_3140_);
lean_dec_ref_known(v_e_3094_, 1);
v___x_3141_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3140_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3141_;
}
case 3:
{
lean_object* v_u_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_u_3142_ = lean_ctor_get(v_e_3094_, 0);
lean_inc(v_u_3142_);
lean_dec_ref_known(v_e_3094_, 1);
v___x_3143_ = l_Lean_Level_succ___override(v_u_3142_);
v___x_3144_ = l_Lean_mkSort(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
return v___x_3145_;
}
case 4:
{
lean_object* v_declName_3146_; lean_object* v_us_3147_; 
v_declName_3146_ = lean_ctor_get(v_e_3094_, 0);
lean_inc(v_declName_3146_);
v_us_3147_ = lean_ctor_get(v_e_3094_, 1);
lean_inc(v_us_3147_);
if (lean_obj_tag(v_us_3147_) == 0)
{
lean_object* v___x_3164_; 
lean_dec_ref_known(v_e_3094_, 2);
v___x_3164_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3146_, v_us_3147_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3164_;
}
else
{
uint8_t v_cacheInferType_3165_; 
v_cacheInferType_3165_ = lean_ctor_get_uint8(v_a_3095_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3165_ == 0)
{
lean_dec_ref_known(v_e_3094_, 2);
goto v___jp_3148_;
}
else
{
uint8_t v___x_3166_; 
v___x_3166_ = l_Lean_Expr_hasMVar(v_e_3094_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3233_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3233_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3233_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3212_; lean_object* v_cache_3213_; lean_object* v_inferType_3214_; lean_object* v___x_3215_; 
v___x_3212_ = lean_st_ref_get(v_a_3096_);
v_cache_3213_ = lean_ctor_get(v___x_3212_, 1);
lean_inc_ref(v_cache_3213_);
lean_dec(v___x_3212_);
v_inferType_3214_ = lean_ctor_get(v_cache_3213_, 0);
lean_inc_ref(v_inferType_3214_);
lean_dec_ref(v_cache_3213_);
v___x_3215_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3214_, v_a_3168_);
lean_dec_ref(v_inferType_3214_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_toCold_3216_; lean_object* v_cancelTk_x3f_3217_; 
lean_del_object(v___x_3170_);
v_toCold_3216_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3217_ = lean_ctor_get(v_toCold_3216_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3217_) == 1)
{
lean_object* v_val_3218_; uint8_t v___x_3219_; 
v_val_3218_ = lean_ctor_get(v_cancelTk_x3f_3217_, 0);
v___x_3219_ = l_IO_CancelToken_isSet(v_val_3218_);
if (v___x_3219_ == 0)
{
goto v___jp_3172_;
}
else
{
lean_object* v___x_3220_; lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_a_3168_);
lean_dec(v_us_3147_);
lean_dec(v_declName_3146_);
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
goto v___jp_3172_;
}
}
else
{
lean_object* v_val_3229_; lean_object* v___x_3231_; 
lean_dec(v_a_3168_);
lean_dec(v_us_3147_);
lean_dec(v_declName_3146_);
v_val_3229_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___x_3215_, 1);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 0, v_val_3229_);
v___x_3231_ = v___x_3170_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_val_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
v___jp_3172_:
{
lean_object* v___x_3173_; 
v___x_3173_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3146_, v_us_3147_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; uint8_t v___x_3175_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v___x_3175_ = l_Lean_Expr_hasMVar(v_a_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3210_; 
lean_inc(v_a_3174_);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v___x_3173_, 0);
lean_dec(v_unused_3211_);
v___x_3177_ = v___x_3173_;
v_isShared_3178_ = v_isSharedCheck_3210_;
goto v_resetjp_3176_;
}
else
{
lean_dec(v___x_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3210_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v_cache_3180_; lean_object* v_mctx_3181_; lean_object* v_zetaDeltaFVarIds_3182_; lean_object* v_postponed_3183_; lean_object* v_diag_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3209_; 
v___x_3179_ = lean_st_ref_take(v_a_3096_);
v_cache_3180_ = lean_ctor_get(v___x_3179_, 1);
v_mctx_3181_ = lean_ctor_get(v___x_3179_, 0);
v_zetaDeltaFVarIds_3182_ = lean_ctor_get(v___x_3179_, 2);
v_postponed_3183_ = lean_ctor_get(v___x_3179_, 3);
v_diag_3184_ = lean_ctor_get(v___x_3179_, 4);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3186_ = v___x_3179_;
v_isShared_3187_ = v_isSharedCheck_3209_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_diag_3184_);
lean_inc(v_postponed_3183_);
lean_inc(v_zetaDeltaFVarIds_3182_);
lean_inc(v_cache_3180_);
lean_inc(v_mctx_3181_);
lean_dec(v___x_3179_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3209_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_inferType_3188_; lean_object* v_funInfo_3189_; lean_object* v_synthInstance_3190_; lean_object* v_whnf_3191_; lean_object* v_defEqTrans_3192_; lean_object* v_defEqPerm_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3208_; 
v_inferType_3188_ = lean_ctor_get(v_cache_3180_, 0);
v_funInfo_3189_ = lean_ctor_get(v_cache_3180_, 1);
v_synthInstance_3190_ = lean_ctor_get(v_cache_3180_, 2);
v_whnf_3191_ = lean_ctor_get(v_cache_3180_, 3);
v_defEqTrans_3192_ = lean_ctor_get(v_cache_3180_, 4);
v_defEqPerm_3193_ = lean_ctor_get(v_cache_3180_, 5);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_cache_3180_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3195_ = v_cache_3180_;
v_isShared_3196_ = v_isSharedCheck_3208_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_defEqPerm_3193_);
lean_inc(v_defEqTrans_3192_);
lean_inc(v_whnf_3191_);
lean_inc(v_synthInstance_3190_);
lean_inc(v_funInfo_3189_);
lean_inc(v_inferType_3188_);
lean_dec(v_cache_3180_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3208_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_inc(v_a_3174_);
v___x_3197_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3188_, v_a_3168_, v_a_3174_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3197_);
v___x_3199_ = v___x_3195_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_funInfo_3189_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_synthInstance_3190_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_whnf_3191_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v_defEqTrans_3192_);
lean_ctor_set(v_reuseFailAlloc_3207_, 5, v_defEqPerm_3193_);
v___x_3199_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 1, v___x_3199_);
v___x_3201_ = v___x_3186_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_mctx_3181_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_zetaDeltaFVarIds_3182_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v_postponed_3183_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v_diag_3184_);
v___x_3201_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3202_ = lean_st_ref_put(v_a_3096_, v___x_3201_);
if (v_isShared_3178_ == 0)
{
v___x_3204_ = v___x_3177_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3174_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3168_);
return v___x_3173_;
}
}
else
{
lean_dec(v_a_3168_);
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_us_3147_);
lean_dec(v_declName_3146_);
v_a_3234_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3167_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3167_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3094_, 2);
goto v___jp_3148_;
}
}
}
v___jp_3148_:
{
lean_object* v_toCold_3149_; lean_object* v_cancelTk_x3f_3150_; 
v_toCold_3149_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3150_ = lean_ctor_get(v_toCold_3149_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3150_) == 1)
{
lean_object* v_val_3151_; uint8_t v___x_3152_; 
v_val_3151_ = lean_ctor_get(v_cancelTk_x3f_3150_, 0);
v___x_3152_ = l_IO_CancelToken_isSet(v_val_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3146_, v_us_3147_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3153_;
}
else
{
lean_object* v___x_3154_; lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_us_3147_);
lean_dec(v_declName_3146_);
v___x_3154_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v___x_3163_; 
v___x_3163_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3146_, v_us_3147_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3163_;
}
}
}
case 5:
{
lean_object* v_fn_3242_; uint8_t v_cacheInferType_3243_; lean_object* v_nargs_3244_; lean_object* v___x_3245_; lean_object* v_dummy_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_fn_3242_ = lean_ctor_get(v_e_3094_, 0);
v_cacheInferType_3243_ = lean_ctor_get_uint8(v_a_3095_, sizeof(void*)*7 + 3);
v_nargs_3244_ = l_Lean_Expr_getAppNumArgs(v_e_3094_);
v___x_3245_ = l_Lean_Expr_getAppFn(v_fn_3242_);
v_dummy_3246_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3244_);
v___x_3247_ = lean_mk_array(v_nargs_3244_, v_dummy_3246_);
v___x_3248_ = lean_unsigned_to_nat(1u);
v___x_3249_ = lean_nat_sub(v_nargs_3244_, v___x_3248_);
lean_dec(v_nargs_3244_);
lean_inc_ref(v_e_3094_);
v___x_3250_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3094_, v___x_3247_, v___x_3249_);
if (v_cacheInferType_3243_ == 0)
{
lean_dec_ref_known(v_e_3094_, 2);
goto v___jp_3251_;
}
else
{
uint8_t v___x_3267_; 
v___x_3267_ = l_Lean_Expr_hasMVar(v_e_3094_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3334_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3334_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3334_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3313_; lean_object* v_cache_3314_; lean_object* v_inferType_3315_; lean_object* v___x_3316_; 
v___x_3313_ = lean_st_ref_get(v_a_3096_);
v_cache_3314_ = lean_ctor_get(v___x_3313_, 1);
lean_inc_ref(v_cache_3314_);
lean_dec(v___x_3313_);
v_inferType_3315_ = lean_ctor_get(v_cache_3314_, 0);
lean_inc_ref(v_inferType_3315_);
lean_dec_ref(v_cache_3314_);
v___x_3316_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3315_, v_a_3269_);
lean_dec_ref(v_inferType_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_toCold_3317_; lean_object* v_cancelTk_x3f_3318_; 
lean_del_object(v___x_3271_);
v_toCold_3317_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3318_ = lean_ctor_get(v_toCold_3317_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3318_) == 1)
{
lean_object* v_val_3319_; uint8_t v___x_3320_; 
v_val_3319_ = lean_ctor_get(v_cancelTk_x3f_3318_, 0);
v___x_3320_ = l_IO_CancelToken_isSet(v_val_3319_);
if (v___x_3320_ == 0)
{
goto v___jp_3273_;
}
else
{
lean_object* v___x_3321_; lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v_a_3269_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3245_);
v___x_3321_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
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
else
{
goto v___jp_3273_;
}
}
else
{
lean_object* v_val_3330_; lean_object* v___x_3332_; 
lean_dec(v_a_3269_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3245_);
v_val_3330_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v___x_3316_, 1);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v_val_3330_);
v___x_3332_ = v___x_3271_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_val_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
v___jp_3273_:
{
lean_object* v___x_3274_; 
v___x_3274_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3245_, v___x_3250_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec_ref(v___x_3250_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; uint8_t v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v___x_3276_ = l_Lean_Expr_hasMVar(v_a_3275_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3311_; 
lean_inc(v_a_3275_);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3311_ == 0)
{
lean_object* v_unused_3312_; 
v_unused_3312_ = lean_ctor_get(v___x_3274_, 0);
lean_dec(v_unused_3312_);
v___x_3278_ = v___x_3274_;
v_isShared_3279_ = v_isSharedCheck_3311_;
goto v_resetjp_3277_;
}
else
{
lean_dec(v___x_3274_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3311_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v_cache_3281_; lean_object* v_mctx_3282_; lean_object* v_zetaDeltaFVarIds_3283_; lean_object* v_postponed_3284_; lean_object* v_diag_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3310_; 
v___x_3280_ = lean_st_ref_take(v_a_3096_);
v_cache_3281_ = lean_ctor_get(v___x_3280_, 1);
v_mctx_3282_ = lean_ctor_get(v___x_3280_, 0);
v_zetaDeltaFVarIds_3283_ = lean_ctor_get(v___x_3280_, 2);
v_postponed_3284_ = lean_ctor_get(v___x_3280_, 3);
v_diag_3285_ = lean_ctor_get(v___x_3280_, 4);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3287_ = v___x_3280_;
v_isShared_3288_ = v_isSharedCheck_3310_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_diag_3285_);
lean_inc(v_postponed_3284_);
lean_inc(v_zetaDeltaFVarIds_3283_);
lean_inc(v_cache_3281_);
lean_inc(v_mctx_3282_);
lean_dec(v___x_3280_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3310_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v_inferType_3289_; lean_object* v_funInfo_3290_; lean_object* v_synthInstance_3291_; lean_object* v_whnf_3292_; lean_object* v_defEqTrans_3293_; lean_object* v_defEqPerm_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3309_; 
v_inferType_3289_ = lean_ctor_get(v_cache_3281_, 0);
v_funInfo_3290_ = lean_ctor_get(v_cache_3281_, 1);
v_synthInstance_3291_ = lean_ctor_get(v_cache_3281_, 2);
v_whnf_3292_ = lean_ctor_get(v_cache_3281_, 3);
v_defEqTrans_3293_ = lean_ctor_get(v_cache_3281_, 4);
v_defEqPerm_3294_ = lean_ctor_get(v_cache_3281_, 5);
v_isSharedCheck_3309_ = !lean_is_exclusive(v_cache_3281_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3296_ = v_cache_3281_;
v_isShared_3297_ = v_isSharedCheck_3309_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_defEqPerm_3294_);
lean_inc(v_defEqTrans_3293_);
lean_inc(v_whnf_3292_);
lean_inc(v_synthInstance_3291_);
lean_inc(v_funInfo_3290_);
lean_inc(v_inferType_3289_);
lean_dec(v_cache_3281_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3309_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
lean_inc(v_a_3275_);
v___x_3298_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3289_, v_a_3269_, v_a_3275_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v___x_3298_);
v___x_3300_ = v___x_3296_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_funInfo_3290_);
lean_ctor_set(v_reuseFailAlloc_3308_, 2, v_synthInstance_3291_);
lean_ctor_set(v_reuseFailAlloc_3308_, 3, v_whnf_3292_);
lean_ctor_set(v_reuseFailAlloc_3308_, 4, v_defEqTrans_3293_);
lean_ctor_set(v_reuseFailAlloc_3308_, 5, v_defEqPerm_3294_);
v___x_3300_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3302_; 
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 1, v___x_3300_);
v___x_3302_ = v___x_3287_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_mctx_3282_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3307_, 2, v_zetaDeltaFVarIds_3283_);
lean_ctor_set(v_reuseFailAlloc_3307_, 3, v_postponed_3284_);
lean_ctor_set(v_reuseFailAlloc_3307_, 4, v_diag_3285_);
v___x_3302_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3303_ = lean_st_ref_put(v_a_3096_, v___x_3302_);
if (v_isShared_3279_ == 0)
{
v___x_3305_ = v___x_3278_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3275_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3269_);
return v___x_3274_;
}
}
else
{
lean_dec(v_a_3269_);
return v___x_3274_;
}
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3245_);
v_a_3335_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3268_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3268_);
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
lean_dec_ref_known(v_e_3094_, 2);
goto v___jp_3251_;
}
}
v___jp_3251_:
{
lean_object* v_toCold_3252_; lean_object* v_cancelTk_x3f_3253_; 
v_toCold_3252_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3253_ = lean_ctor_get(v_toCold_3252_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3253_) == 1)
{
lean_object* v_val_3254_; uint8_t v___x_3255_; 
v_val_3254_ = lean_ctor_get(v_cancelTk_x3f_3253_, 0);
v___x_3255_ = l_IO_CancelToken_isSet(v_val_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3245_, v___x_3250_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec_ref(v___x_3250_);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3245_);
v___x_3257_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
else
{
lean_object* v___x_3266_; 
v___x_3266_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3245_, v___x_3250_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
lean_dec_ref(v___x_3250_);
return v___x_3266_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3343_; 
v_cacheInferType_3343_ = lean_ctor_get_uint8(v_a_3095_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3343_ == 0)
{
goto v___jp_3116_;
}
else
{
uint8_t v___x_3344_; 
v___x_3344_ = l_Lean_Expr_hasMVar(v_e_3094_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_inc_ref(v_e_3094_);
v___x_3345_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3411_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3411_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3411_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3390_; lean_object* v_cache_3391_; lean_object* v_inferType_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_st_ref_get(v_a_3096_);
v_cache_3391_ = lean_ctor_get(v___x_3390_, 1);
lean_inc_ref(v_cache_3391_);
lean_dec(v___x_3390_);
v_inferType_3392_ = lean_ctor_get(v_cache_3391_, 0);
lean_inc_ref(v_inferType_3392_);
lean_dec_ref(v_cache_3391_);
v___x_3393_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3392_, v_a_3346_);
lean_dec_ref(v_inferType_3392_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_toCold_3394_; lean_object* v_cancelTk_x3f_3395_; 
lean_del_object(v___x_3348_);
v_toCold_3394_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3395_ = lean_ctor_get(v_toCold_3394_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3395_) == 1)
{
lean_object* v_val_3396_; uint8_t v___x_3397_; 
v_val_3396_ = lean_ctor_get(v_cancelTk_x3f_3395_, 0);
v___x_3397_ = l_IO_CancelToken_isSet(v_val_3396_);
if (v___x_3397_ == 0)
{
goto v___jp_3350_;
}
else
{
lean_object* v___x_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_a_3346_);
lean_dec_ref_known(v_e_3094_, 3);
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
goto v___jp_3350_;
}
}
else
{
lean_object* v_val_3407_; lean_object* v___x_3409_; 
lean_dec(v_a_3346_);
lean_dec_ref_known(v_e_3094_, 3);
v_val_3407_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v___x_3393_, 1);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_val_3407_);
v___x_3409_ = v___x_3348_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_val_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
v___jp_3350_:
{
lean_object* v___x_3351_; 
v___x_3351_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; uint8_t v___x_3353_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v___x_3353_ = l_Lean_Expr_hasMVar(v_a_3352_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3388_; 
lean_inc(v_a_3352_);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v___x_3351_, 0);
lean_dec(v_unused_3389_);
v___x_3355_ = v___x_3351_;
v_isShared_3356_ = v_isSharedCheck_3388_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v___x_3351_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3388_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v_cache_3358_; lean_object* v_mctx_3359_; lean_object* v_zetaDeltaFVarIds_3360_; lean_object* v_postponed_3361_; lean_object* v_diag_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3387_; 
v___x_3357_ = lean_st_ref_take(v_a_3096_);
v_cache_3358_ = lean_ctor_get(v___x_3357_, 1);
v_mctx_3359_ = lean_ctor_get(v___x_3357_, 0);
v_zetaDeltaFVarIds_3360_ = lean_ctor_get(v___x_3357_, 2);
v_postponed_3361_ = lean_ctor_get(v___x_3357_, 3);
v_diag_3362_ = lean_ctor_get(v___x_3357_, 4);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3364_ = v___x_3357_;
v_isShared_3365_ = v_isSharedCheck_3387_;
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
v_isShared_3365_ = v_isSharedCheck_3387_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_inferType_3366_; lean_object* v_funInfo_3367_; lean_object* v_synthInstance_3368_; lean_object* v_whnf_3369_; lean_object* v_defEqTrans_3370_; lean_object* v_defEqPerm_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3386_; 
v_inferType_3366_ = lean_ctor_get(v_cache_3358_, 0);
v_funInfo_3367_ = lean_ctor_get(v_cache_3358_, 1);
v_synthInstance_3368_ = lean_ctor_get(v_cache_3358_, 2);
v_whnf_3369_ = lean_ctor_get(v_cache_3358_, 3);
v_defEqTrans_3370_ = lean_ctor_get(v_cache_3358_, 4);
v_defEqPerm_3371_ = lean_ctor_get(v_cache_3358_, 5);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_cache_3358_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3373_ = v_cache_3358_;
v_isShared_3374_ = v_isSharedCheck_3386_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_defEqPerm_3371_);
lean_inc(v_defEqTrans_3370_);
lean_inc(v_whnf_3369_);
lean_inc(v_synthInstance_3368_);
lean_inc(v_funInfo_3367_);
lean_inc(v_inferType_3366_);
lean_dec(v_cache_3358_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3386_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
lean_inc(v_a_3352_);
v___x_3375_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3366_, v_a_3346_, v_a_3352_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3375_);
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_funInfo_3367_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_synthInstance_3368_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_whnf_3369_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v_defEqTrans_3370_);
lean_ctor_set(v_reuseFailAlloc_3385_, 5, v_defEqPerm_3371_);
v___x_3377_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v___x_3377_);
v___x_3379_ = v___x_3364_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_mctx_3359_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3384_, 2, v_zetaDeltaFVarIds_3360_);
lean_ctor_set(v_reuseFailAlloc_3384_, 3, v_postponed_3361_);
lean_ctor_set(v_reuseFailAlloc_3384_, 4, v_diag_3362_);
v___x_3379_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3380_ = lean_st_ref_put(v_a_3096_, v___x_3379_);
if (v_isShared_3356_ == 0)
{
v___x_3382_ = v___x_3355_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3352_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
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
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec_ref_known(v_e_3094_, 3);
v_a_3412_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3345_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3345_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
else
{
goto v___jp_3116_;
}
}
}
case 9:
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_a_3420_ = lean_ctor_get(v_e_3094_, 0);
lean_inc_ref(v_a_3420_);
lean_dec_ref_known(v_e_3094_, 1);
v___x_3421_ = l_Lean_Literal_type(v_a_3420_);
lean_dec_ref(v_a_3420_);
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
case 10:
{
lean_object* v_expr_3423_; 
v_expr_3423_ = lean_ctor_get(v_e_3094_, 1);
lean_inc_ref(v_expr_3423_);
lean_dec_ref_known(v_e_3094_, 2);
v_e_3094_ = v_expr_3423_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3425_; lean_object* v_idx_3426_; lean_object* v_struct_3427_; uint8_t v_cacheInferType_3444_; 
v_typeName_3425_ = lean_ctor_get(v_e_3094_, 0);
lean_inc(v_typeName_3425_);
v_idx_3426_ = lean_ctor_get(v_e_3094_, 1);
lean_inc(v_idx_3426_);
v_struct_3427_ = lean_ctor_get(v_e_3094_, 2);
lean_inc_ref(v_struct_3427_);
v_cacheInferType_3444_ = lean_ctor_get_uint8(v_a_3095_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3444_ == 0)
{
lean_dec_ref_known(v_e_3094_, 3);
goto v___jp_3428_;
}
else
{
uint8_t v___x_3445_; 
v___x_3445_ = l_Lean_Expr_hasMVar(v_e_3094_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3512_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3512_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3512_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3491_; lean_object* v_cache_3492_; lean_object* v_inferType_3493_; lean_object* v___x_3494_; 
v___x_3491_ = lean_st_ref_get(v_a_3096_);
v_cache_3492_ = lean_ctor_get(v___x_3491_, 1);
lean_inc_ref(v_cache_3492_);
lean_dec(v___x_3491_);
v_inferType_3493_ = lean_ctor_get(v_cache_3492_, 0);
lean_inc_ref(v_inferType_3493_);
lean_dec_ref(v_cache_3492_);
v___x_3494_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3493_, v_a_3447_);
lean_dec_ref(v_inferType_3493_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_toCold_3495_; lean_object* v_cancelTk_x3f_3496_; 
lean_del_object(v___x_3449_);
v_toCold_3495_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3496_ = lean_ctor_get(v_toCold_3495_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3496_) == 1)
{
lean_object* v_val_3497_; uint8_t v___x_3498_; 
v_val_3497_ = lean_ctor_get(v_cancelTk_x3f_3496_, 0);
v___x_3498_ = l_IO_CancelToken_isSet(v_val_3497_);
if (v___x_3498_ == 0)
{
goto v___jp_3451_;
}
else
{
lean_object* v___x_3499_; lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec(v_a_3447_);
lean_dec_ref(v_struct_3427_);
lean_dec(v_idx_3426_);
lean_dec(v_typeName_3425_);
v___x_3499_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
goto v___jp_3451_;
}
}
else
{
lean_object* v_val_3508_; lean_object* v___x_3510_; 
lean_dec(v_a_3447_);
lean_dec_ref(v_struct_3427_);
lean_dec(v_idx_3426_);
lean_dec(v_typeName_3425_);
v_val_3508_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_val_3508_);
lean_dec_ref_known(v___x_3494_, 1);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v_val_3508_);
v___x_3510_ = v___x_3449_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_val_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
v___jp_3451_:
{
lean_object* v___x_3452_; 
v___x_3452_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3425_, v_idx_3426_, v_struct_3427_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; uint8_t v___x_3454_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v___x_3454_ = l_Lean_Expr_hasMVar(v_a_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3489_; 
lean_inc(v_a_3453_);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v___x_3452_, 0);
lean_dec(v_unused_3490_);
v___x_3456_ = v___x_3452_;
v_isShared_3457_ = v_isSharedCheck_3489_;
goto v_resetjp_3455_;
}
else
{
lean_dec(v___x_3452_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3489_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v_cache_3459_; lean_object* v_mctx_3460_; lean_object* v_zetaDeltaFVarIds_3461_; lean_object* v_postponed_3462_; lean_object* v_diag_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3488_; 
v___x_3458_ = lean_st_ref_take(v_a_3096_);
v_cache_3459_ = lean_ctor_get(v___x_3458_, 1);
v_mctx_3460_ = lean_ctor_get(v___x_3458_, 0);
v_zetaDeltaFVarIds_3461_ = lean_ctor_get(v___x_3458_, 2);
v_postponed_3462_ = lean_ctor_get(v___x_3458_, 3);
v_diag_3463_ = lean_ctor_get(v___x_3458_, 4);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3465_ = v___x_3458_;
v_isShared_3466_ = v_isSharedCheck_3488_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_diag_3463_);
lean_inc(v_postponed_3462_);
lean_inc(v_zetaDeltaFVarIds_3461_);
lean_inc(v_cache_3459_);
lean_inc(v_mctx_3460_);
lean_dec(v___x_3458_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3488_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v_inferType_3467_; lean_object* v_funInfo_3468_; lean_object* v_synthInstance_3469_; lean_object* v_whnf_3470_; lean_object* v_defEqTrans_3471_; lean_object* v_defEqPerm_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3487_; 
v_inferType_3467_ = lean_ctor_get(v_cache_3459_, 0);
v_funInfo_3468_ = lean_ctor_get(v_cache_3459_, 1);
v_synthInstance_3469_ = lean_ctor_get(v_cache_3459_, 2);
v_whnf_3470_ = lean_ctor_get(v_cache_3459_, 3);
v_defEqTrans_3471_ = lean_ctor_get(v_cache_3459_, 4);
v_defEqPerm_3472_ = lean_ctor_get(v_cache_3459_, 5);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_cache_3459_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3474_ = v_cache_3459_;
v_isShared_3475_ = v_isSharedCheck_3487_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_defEqPerm_3472_);
lean_inc(v_defEqTrans_3471_);
lean_inc(v_whnf_3470_);
lean_inc(v_synthInstance_3469_);
lean_inc(v_funInfo_3468_);
lean_inc(v_inferType_3467_);
lean_dec(v_cache_3459_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3487_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
lean_inc(v_a_3453_);
v___x_3476_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3467_, v_a_3447_, v_a_3453_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3476_);
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_funInfo_3468_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_synthInstance_3469_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_whnf_3470_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_defEqTrans_3471_);
lean_ctor_set(v_reuseFailAlloc_3486_, 5, v_defEqPerm_3472_);
v___x_3478_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 1, v___x_3478_);
v___x_3480_ = v___x_3465_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_mctx_3460_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_zetaDeltaFVarIds_3461_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_postponed_3462_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_diag_3463_);
v___x_3480_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3481_ = lean_st_ref_put(v_a_3096_, v___x_3480_);
if (v_isShared_3457_ == 0)
{
v___x_3483_ = v___x_3456_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3453_);
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
}
}
}
else
{
lean_dec(v_a_3447_);
return v___x_3452_;
}
}
else
{
lean_dec(v_a_3447_);
return v___x_3452_;
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_struct_3427_);
lean_dec(v_idx_3426_);
lean_dec(v_typeName_3425_);
v_a_3513_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3446_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3446_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3094_, 3);
goto v___jp_3428_;
}
}
v___jp_3428_:
{
lean_object* v_toCold_3429_; lean_object* v_cancelTk_x3f_3430_; 
v_toCold_3429_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3430_ = lean_ctor_get(v_toCold_3429_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3430_) == 1)
{
lean_object* v_val_3431_; uint8_t v___x_3432_; 
v_val_3431_ = lean_ctor_get(v_cancelTk_x3f_3430_, 0);
v___x_3432_ = l_IO_CancelToken_isSet(v_val_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; 
v___x_3433_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3425_, v_idx_3426_, v_struct_3427_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3433_;
}
else
{
lean_object* v___x_3434_; lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v_struct_3427_);
lean_dec(v_idx_3426_);
lean_dec(v_typeName_3425_);
v___x_3434_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
lean_object* v___x_3443_; 
v___x_3443_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3425_, v_idx_3426_, v_struct_3427_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3443_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3521_; 
v_cacheInferType_3521_ = lean_ctor_get_uint8(v_a_3095_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3521_ == 0)
{
goto v___jp_3100_;
}
else
{
uint8_t v___x_3522_; 
v___x_3522_ = l_Lean_Expr_hasMVar(v_e_3094_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_inc_ref(v_e_3094_);
v___x_3523_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3094_, v_a_3095_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3589_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3589_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3589_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3568_; lean_object* v_cache_3569_; lean_object* v_inferType_3570_; lean_object* v___x_3571_; 
v___x_3568_ = lean_st_ref_get(v_a_3096_);
v_cache_3569_ = lean_ctor_get(v___x_3568_, 1);
lean_inc_ref(v_cache_3569_);
lean_dec(v___x_3568_);
v_inferType_3570_ = lean_ctor_get(v_cache_3569_, 0);
lean_inc_ref(v_inferType_3570_);
lean_dec_ref(v_cache_3569_);
v___x_3571_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3570_, v_a_3524_);
lean_dec_ref(v_inferType_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_toCold_3572_; lean_object* v_cancelTk_x3f_3573_; 
lean_del_object(v___x_3526_);
v_toCold_3572_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3573_ = lean_ctor_get(v_toCold_3572_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3573_) == 1)
{
lean_object* v_val_3574_; uint8_t v___x_3575_; 
v_val_3574_ = lean_ctor_get(v_cancelTk_x3f_3573_, 0);
v___x_3575_ = l_IO_CancelToken_isSet(v_val_3574_);
if (v___x_3575_ == 0)
{
goto v___jp_3528_;
}
else
{
lean_object* v___x_3576_; lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_a_3524_);
lean_dec_ref(v_e_3094_);
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
goto v___jp_3528_;
}
}
else
{
lean_object* v_val_3585_; lean_object* v___x_3587_; 
lean_dec(v_a_3524_);
lean_dec_ref(v_e_3094_);
v_val_3585_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v___x_3571_, 1);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v_val_3585_);
v___x_3587_ = v___x_3526_;
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
v___jp_3528_:
{
lean_object* v___x_3529_; 
v___x_3529_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; uint8_t v___x_3531_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v___x_3531_ = l_Lean_Expr_hasMVar(v_a_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3566_; 
lean_inc(v_a_3530_);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v___x_3529_, 0);
lean_dec(v_unused_3567_);
v___x_3533_ = v___x_3529_;
v_isShared_3534_ = v_isSharedCheck_3566_;
goto v_resetjp_3532_;
}
else
{
lean_dec(v___x_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3566_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; lean_object* v_cache_3536_; lean_object* v_mctx_3537_; lean_object* v_zetaDeltaFVarIds_3538_; lean_object* v_postponed_3539_; lean_object* v_diag_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3565_; 
v___x_3535_ = lean_st_ref_take(v_a_3096_);
v_cache_3536_ = lean_ctor_get(v___x_3535_, 1);
v_mctx_3537_ = lean_ctor_get(v___x_3535_, 0);
v_zetaDeltaFVarIds_3538_ = lean_ctor_get(v___x_3535_, 2);
v_postponed_3539_ = lean_ctor_get(v___x_3535_, 3);
v_diag_3540_ = lean_ctor_get(v___x_3535_, 4);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3542_ = v___x_3535_;
v_isShared_3543_ = v_isSharedCheck_3565_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_diag_3540_);
lean_inc(v_postponed_3539_);
lean_inc(v_zetaDeltaFVarIds_3538_);
lean_inc(v_cache_3536_);
lean_inc(v_mctx_3537_);
lean_dec(v___x_3535_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3565_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v_inferType_3544_; lean_object* v_funInfo_3545_; lean_object* v_synthInstance_3546_; lean_object* v_whnf_3547_; lean_object* v_defEqTrans_3548_; lean_object* v_defEqPerm_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3564_; 
v_inferType_3544_ = lean_ctor_get(v_cache_3536_, 0);
v_funInfo_3545_ = lean_ctor_get(v_cache_3536_, 1);
v_synthInstance_3546_ = lean_ctor_get(v_cache_3536_, 2);
v_whnf_3547_ = lean_ctor_get(v_cache_3536_, 3);
v_defEqTrans_3548_ = lean_ctor_get(v_cache_3536_, 4);
v_defEqPerm_3549_ = lean_ctor_get(v_cache_3536_, 5);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_cache_3536_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3551_ = v_cache_3536_;
v_isShared_3552_ = v_isSharedCheck_3564_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_defEqPerm_3549_);
lean_inc(v_defEqTrans_3548_);
lean_inc(v_whnf_3547_);
lean_inc(v_synthInstance_3546_);
lean_inc(v_funInfo_3545_);
lean_inc(v_inferType_3544_);
lean_dec(v_cache_3536_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3564_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3555_; 
lean_inc(v_a_3530_);
v___x_3553_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3544_, v_a_3524_, v_a_3530_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3555_ = v___x_3551_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_funInfo_3545_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_synthInstance_3546_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_whnf_3547_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_defEqTrans_3548_);
lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_defEqPerm_3549_);
v___x_3555_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3555_);
v___x_3557_ = v___x_3542_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_mctx_3537_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_zetaDeltaFVarIds_3538_);
lean_ctor_set(v_reuseFailAlloc_3562_, 3, v_postponed_3539_);
lean_ctor_set(v_reuseFailAlloc_3562_, 4, v_diag_3540_);
v___x_3557_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = lean_st_ref_put(v_a_3096_, v___x_3557_);
if (v_isShared_3534_ == 0)
{
v___x_3560_ = v___x_3533_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3530_);
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
lean_dec(v_a_3524_);
return v___x_3529_;
}
}
else
{
lean_dec(v_a_3524_);
return v___x_3529_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_e_3094_);
v_a_3590_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3523_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3523_);
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
goto v___jp_3100_;
}
}
}
}
v___jp_3100_:
{
lean_object* v_toCold_3101_; lean_object* v_cancelTk_x3f_3102_; 
v_toCold_3101_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3102_ = lean_ctor_get(v_toCold_3101_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3102_) == 1)
{
lean_object* v_val_3103_; uint8_t v___x_3104_; 
v_val_3103_ = lean_ctor_get(v_cancelTk_x3f_3102_, 0);
v___x_3104_ = l_IO_CancelToken_isSet(v_val_3103_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref(v_e_3094_);
v___x_3106_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3115_;
}
}
v___jp_3116_:
{
lean_object* v_toCold_3117_; lean_object* v_cancelTk_x3f_3118_; 
v_toCold_3117_ = lean_ctor_get(v_a_3097_, 0);
v_cancelTk_x3f_3118_ = lean_ctor_get(v_toCold_3117_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3118_) == 1)
{
lean_object* v_val_3119_; uint8_t v___x_3120_; 
v_val_3119_ = lean_ctor_get(v_cancelTk_x3f_3118_, 0);
v___x_3120_ = l_IO_CancelToken_isSet(v_val_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_e_3094_);
v___x_3122_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
return v___x_3131_;
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
size_t v_x_3637__boxed_3631_; size_t v_x_3638__boxed_3632_; lean_object* v_res_3633_; 
v_x_3637__boxed_3631_ = lean_unbox_usize(v_x_3627_);
lean_dec(v_x_3627_);
v_x_3638__boxed_3632_ = lean_unbox_usize(v_x_3628_);
lean_dec(v_x_3628_);
v_res_3633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3625_, v_x_3626_, v_x_3637__boxed_3631_, v_x_3638__boxed_3632_, v_x_3629_, v_x_3630_);
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
size_t v_x_3654__boxed_3643_; lean_object* v_res_3644_; 
v_x_3654__boxed_3643_ = lean_unbox_usize(v_x_3641_);
lean_dec(v_x_3641_);
v_res_3644_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3639_, v_x_3640_, v_x_3654__boxed_3643_, v_x_3642_);
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
lean_object* v___y_3804_; lean_object* v_toCold_3821_; lean_object* v_currRecDepth_3822_; lean_object* v_ref_3823_; uint16_t v_optionFlags_3824_; uint8_t v_suppressElabErrors_3825_; uint8_t v_isRecordingDeps_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3866_; 
v_toCold_3821_ = lean_ctor_get(v_a_3800_, 0);
v_currRecDepth_3822_ = lean_ctor_get(v_a_3800_, 1);
v_ref_3823_ = lean_ctor_get(v_a_3800_, 2);
v_optionFlags_3824_ = lean_ctor_get_uint16(v_a_3800_, sizeof(void*)*3);
v_suppressElabErrors_3825_ = lean_ctor_get_uint8(v_a_3800_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3826_ = lean_ctor_get_uint8(v_a_3800_, sizeof(void*)*3 + 3);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3828_ = v_a_3800_;
v_isShared_3829_ = v_isSharedCheck_3866_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_ref_3823_);
lean_inc(v_currRecDepth_3822_);
lean_inc(v_toCold_3821_);
lean_dec(v_a_3800_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3866_;
goto v_resetjp_3827_;
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
v_resetjp_3827_:
{
lean_object* v_maxRecDepth_3830_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_maxRecDepth_3830_ = lean_ctor_get(v_toCold_3821_, 3);
v___x_3862_ = lean_unsigned_to_nat(0u);
v___x_3863_ = lean_nat_dec_eq(v_maxRecDepth_3830_, v___x_3862_);
if (v___x_3863_ == 0)
{
uint8_t v___x_3864_; 
v___x_3864_ = lean_nat_dec_eq(v_currRecDepth_3822_, v_maxRecDepth_3830_);
if (v___x_3864_ == 0)
{
goto v___jp_3831_;
}
else
{
lean_object* v___x_3865_; 
lean_del_object(v___x_3828_);
lean_dec(v_currRecDepth_3822_);
lean_dec_ref(v_toCold_3821_);
lean_dec(v_a_3801_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec_ref(v_e_3797_);
v___x_3865_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3823_);
return v___x_3865_;
}
}
else
{
goto v___jp_3831_;
}
v___jp_3831_:
{
lean_object* v___x_3832_; uint8_t v_transparency_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3832_ = l_Lean_Meta_Context_config(v_a_3798_);
v_transparency_3833_ = lean_ctor_get_uint8(v___x_3832_, 9);
lean_dec_ref(v___x_3832_);
v___x_3834_ = lean_unsigned_to_nat(1u);
v___x_3835_ = lean_nat_add(v_currRecDepth_3822_, v___x_3834_);
lean_dec(v_currRecDepth_3822_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 1, v___x_3835_);
v___x_3837_ = v___x_3828_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_toCold_3821_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3861_, 2, v_ref_3823_);
lean_ctor_set_uint16(v_reuseFailAlloc_3861_, sizeof(void*)*3, v_optionFlags_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3861_, sizeof(void*)*3 + 2, v_suppressElabErrors_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3861_, sizeof(void*)*3 + 3, v_isRecordingDeps_3826_);
v___x_3837_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
uint8_t v___x_3838_; uint8_t v___x_3839_; 
v___x_3838_ = 1;
v___x_3839_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3833_, v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3797_, v_a_3798_, v_a_3799_, v___x_3837_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v___x_3837_);
lean_dec(v_a_3799_);
v___y_3804_ = v___x_3840_;
goto v___jp_3803_;
}
else
{
lean_object* v_keyedConfig_3841_; uint8_t v_trackZetaDelta_3842_; lean_object* v_zetaDeltaSet_3843_; lean_object* v_lctx_3844_; lean_object* v_localInstances_3845_; lean_object* v_defEqCtx_x3f_3846_; lean_object* v_synthPendingDepth_3847_; lean_object* v_customCanUnfoldPredicate_x3f_3848_; uint8_t v_univApprox_3849_; uint8_t v_inTypeClassResolution_3850_; uint8_t v_cacheInferType_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3860_; 
v_keyedConfig_3841_ = lean_ctor_get(v_a_3798_, 0);
v_trackZetaDelta_3842_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7);
v_zetaDeltaSet_3843_ = lean_ctor_get(v_a_3798_, 1);
v_lctx_3844_ = lean_ctor_get(v_a_3798_, 2);
v_localInstances_3845_ = lean_ctor_get(v_a_3798_, 3);
v_defEqCtx_x3f_3846_ = lean_ctor_get(v_a_3798_, 4);
v_synthPendingDepth_3847_ = lean_ctor_get(v_a_3798_, 5);
v_customCanUnfoldPredicate_x3f_3848_ = lean_ctor_get(v_a_3798_, 6);
v_univApprox_3849_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3850_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7 + 2);
v_cacheInferType_3851_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*7 + 3);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_a_3798_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3853_ = v_a_3798_;
v_isShared_3854_ = v_isSharedCheck_3860_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3848_);
lean_inc(v_synthPendingDepth_3847_);
lean_inc(v_defEqCtx_x3f_3846_);
lean_inc(v_localInstances_3845_);
lean_inc(v_lctx_3844_);
lean_inc(v_zetaDeltaSet_3843_);
lean_inc(v_keyedConfig_3841_);
lean_dec(v_a_3798_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3860_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3855_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3838_, v_keyedConfig_3841_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v___x_3855_);
v___x_3857_ = v___x_3853_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3855_);
lean_ctor_set(v_reuseFailAlloc_3859_, 1, v_zetaDeltaSet_3843_);
lean_ctor_set(v_reuseFailAlloc_3859_, 2, v_lctx_3844_);
lean_ctor_set(v_reuseFailAlloc_3859_, 3, v_localInstances_3845_);
lean_ctor_set(v_reuseFailAlloc_3859_, 4, v_defEqCtx_x3f_3846_);
lean_ctor_set(v_reuseFailAlloc_3859_, 5, v_synthPendingDepth_3847_);
lean_ctor_set(v_reuseFailAlloc_3859_, 6, v_customCanUnfoldPredicate_x3f_3848_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, sizeof(void*)*7, v_trackZetaDelta_3842_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, sizeof(void*)*7 + 1, v_univApprox_3849_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3850_);
lean_ctor_set_uint8(v_reuseFailAlloc_3859_, sizeof(void*)*7 + 3, v_cacheInferType_3851_);
v___x_3857_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3797_, v___x_3857_, v_a_3799_, v___x_3837_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v___x_3837_);
lean_dec(v_a_3799_);
v___y_3804_ = v___x_3858_;
goto v___jp_3803_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = lean_infer_type(v_e_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3874_){
_start:
{
switch(lean_obj_tag(v_x_3874_))
{
case 0:
{
uint8_t v___x_3875_; 
v___x_3875_ = 1;
return v___x_3875_;
}
case 2:
{
lean_object* v_a_3876_; lean_object* v_a_3877_; uint8_t v___x_3878_; 
v_a_3876_ = lean_ctor_get(v_x_3874_, 0);
v_a_3877_ = lean_ctor_get(v_x_3874_, 1);
v___x_3878_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3876_);
if (v___x_3878_ == 0)
{
return v___x_3878_;
}
else
{
v_x_3874_ = v_a_3877_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3880_; 
v_a_3880_ = lean_ctor_get(v_x_3874_, 1);
v_x_3874_ = v_a_3880_;
goto _start;
}
default: 
{
uint8_t v___x_3882_; 
v___x_3882_ = 0;
return v___x_3882_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3883_){
_start:
{
uint8_t v_res_3884_; lean_object* v_r_3885_; 
v_res_3884_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3883_);
lean_dec(v_x_3883_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; lean_object* v_mctx_3890_; lean_object* v___x_3891_; lean_object* v_fst_3892_; lean_object* v_snd_3893_; lean_object* v___x_3894_; lean_object* v_cache_3895_; lean_object* v_zetaDeltaFVarIds_3896_; lean_object* v_postponed_3897_; lean_object* v_diag_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3907_; 
v___x_3889_ = lean_st_ref_get(v___y_3887_);
v_mctx_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc_ref(v_mctx_3890_);
lean_dec(v___x_3889_);
v___x_3891_ = lean_instantiate_level_mvars(v_mctx_3890_, v_l_3886_);
v_fst_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_fst_3892_);
v_snd_3893_ = lean_ctor_get(v___x_3891_, 1);
lean_inc(v_snd_3893_);
lean_dec_ref(v___x_3891_);
v___x_3894_ = lean_st_ref_take(v___y_3887_);
v_cache_3895_ = lean_ctor_get(v___x_3894_, 1);
v_zetaDeltaFVarIds_3896_ = lean_ctor_get(v___x_3894_, 2);
v_postponed_3897_ = lean_ctor_get(v___x_3894_, 3);
v_diag_3898_ = lean_ctor_get(v___x_3894_, 4);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v___x_3894_, 0);
lean_dec(v_unused_3908_);
v___x_3900_ = v___x_3894_;
v_isShared_3901_ = v_isSharedCheck_3907_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_diag_3898_);
lean_inc(v_postponed_3897_);
lean_inc(v_zetaDeltaFVarIds_3896_);
lean_inc(v_cache_3895_);
lean_dec(v___x_3894_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3907_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v_fst_3892_);
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_fst_3892_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_cache_3895_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_zetaDeltaFVarIds_3896_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v_postponed_3897_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v_diag_3898_);
v___x_3903_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_st_ref_put(v___y_3887_, v___x_3903_);
v___x_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3905_, 0, v_snd_3893_);
return v___x_3905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3909_, v___y_3910_);
lean_dec(v___y_3910_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3913_, v___y_3915_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3927_, lean_object* v_x_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
switch(lean_obj_tag(v_x_3927_))
{
case 3:
{
lean_object* v_u_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; 
v_u_3938_ = lean_ctor_get(v_x_3927_, 0);
lean_inc(v_u_3938_);
lean_dec_ref_known(v_x_3927_, 1);
v___x_3939_ = lean_unsigned_to_nat(0u);
v___x_3940_ = lean_nat_dec_eq(v_x_3928_, v___x_3939_);
lean_dec(v_x_3928_);
if (v___x_3940_ == 0)
{
lean_dec(v_u_3938_);
goto v___jp_3934_;
}
else
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3938_, v_a_3930_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3952_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3952_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3952_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
uint8_t v___x_3946_; uint8_t v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3950_; 
v___x_3946_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3942_);
lean_dec(v_a_3942_);
v___x_3947_ = l_Lean_Bool_toLBool(v___x_3946_);
v___x_3948_ = lean_box(v___x_3947_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v___x_3948_);
v___x_3950_ = v___x_3944_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3948_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
v_a_3953_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3941_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3941_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3961_; lean_object* v_zero_3962_; uint8_t v_isZero_3963_; 
v_body_3961_ = lean_ctor_get(v_x_3927_, 2);
lean_inc_ref(v_body_3961_);
lean_dec_ref_known(v_x_3927_, 3);
v_zero_3962_ = lean_unsigned_to_nat(0u);
v_isZero_3963_ = lean_nat_dec_eq(v_x_3928_, v_zero_3962_);
if (v_isZero_3963_ == 1)
{
uint8_t v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_dec_ref(v_body_3961_);
lean_dec(v_x_3928_);
v___x_3964_ = 0;
v___x_3965_ = lean_box(v___x_3964_);
v___x_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
return v___x_3966_;
}
else
{
lean_object* v_one_3967_; lean_object* v_n_3968_; 
v_one_3967_ = lean_unsigned_to_nat(1u);
v_n_3968_ = lean_nat_sub(v_x_3928_, v_one_3967_);
lean_dec(v_x_3928_);
v_x_3927_ = v_body_3961_;
v_x_3928_ = v_n_3968_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3970_; 
v_body_3970_ = lean_ctor_get(v_x_3927_, 3);
lean_inc_ref(v_body_3970_);
lean_dec_ref_known(v_x_3927_, 4);
v_x_3927_ = v_body_3970_;
goto _start;
}
case 10:
{
lean_object* v_expr_3972_; 
v_expr_3972_ = lean_ctor_get(v_x_3927_, 1);
lean_inc_ref(v_expr_3972_);
lean_dec_ref_known(v_x_3927_, 2);
v_x_3927_ = v_expr_3972_;
goto _start;
}
default: 
{
lean_dec(v_x_3928_);
lean_dec_ref(v_x_3927_);
goto v___jp_3934_;
}
}
v___jp_3934_:
{
uint8_t v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3935_ = 2;
v___x_3936_ = lean_box(v___x_3935_);
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3974_, lean_object* v_x_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3974_, v_x_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3982_, lean_object* v_x_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
switch(lean_obj_tag(v_x_3982_))
{
case 4:
{
lean_object* v_declName_3989_; lean_object* v_us_3990_; lean_object* v___x_3991_; 
v_declName_3989_ = lean_ctor_get(v_x_3982_, 0);
lean_inc(v_declName_3989_);
v_us_3990_ = lean_ctor_get(v_x_3982_, 1);
lean_inc(v_us_3990_);
lean_dec_ref_known(v_x_3982_, 2);
v___x_3991_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3989_, v_us_3990_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___x_3993_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___x_3991_, 1);
v___x_3993_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3992_, v_x_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
return v___x_3993_;
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec(v_x_3983_);
v_a_3994_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3991_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3991_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4002_; lean_object* v___x_4003_; 
v_fvarId_4002_ = lean_ctor_get(v_x_3982_, 0);
lean_inc(v_fvarId_4002_);
lean_dec_ref_known(v_x_3982_, 1);
v___x_4003_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4002_, v_a_3984_, v_a_3986_, v_a_3987_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4005_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
v___x_4005_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4004_, v_x_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
return v___x_4005_;
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec(v_x_3983_);
v_a_4006_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4003_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4003_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4014_; lean_object* v___x_4015_; 
v_mvarId_4014_ = lean_ctor_get(v_x_3982_, 0);
lean_inc(v_mvarId_4014_);
lean_dec_ref_known(v_x_3982_, 1);
v___x_4015_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4014_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4017_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v___x_4017_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4016_, v_x_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
return v___x_4017_;
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_x_3983_);
v_a_4018_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4015_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4015_);
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
case 5:
{
lean_object* v_fn_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_fn_4026_ = lean_ctor_get(v_x_3982_, 0);
lean_inc_ref(v_fn_4026_);
lean_dec_ref_known(v_x_3982_, 2);
v___x_4027_ = lean_unsigned_to_nat(1u);
v___x_4028_ = lean_nat_add(v_x_3983_, v___x_4027_);
lean_dec(v_x_3983_);
v_x_3982_ = v_fn_4026_;
v_x_3983_ = v___x_4028_;
goto _start;
}
case 10:
{
lean_object* v_expr_4030_; 
v_expr_4030_ = lean_ctor_get(v_x_3982_, 1);
lean_inc_ref(v_expr_4030_);
lean_dec_ref_known(v_x_3982_, 2);
v_x_3982_ = v_expr_4030_;
goto _start;
}
case 8:
{
lean_object* v_body_4032_; 
v_body_4032_ = lean_ctor_get(v_x_3982_, 3);
lean_inc_ref(v_body_4032_);
lean_dec_ref_known(v_x_3982_, 4);
v_x_3982_ = v_body_4032_;
goto _start;
}
case 6:
{
lean_object* v_body_4034_; lean_object* v_zero_4035_; uint8_t v_isZero_4036_; 
v_body_4034_ = lean_ctor_get(v_x_3982_, 2);
lean_inc_ref(v_body_4034_);
lean_dec_ref_known(v_x_3982_, 3);
v_zero_4035_ = lean_unsigned_to_nat(0u);
v_isZero_4036_ = lean_nat_dec_eq(v_x_3983_, v_zero_4035_);
if (v_isZero_4036_ == 1)
{
uint8_t v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec_ref(v_body_4034_);
lean_dec(v_x_3983_);
v___x_4037_ = 0;
v___x_4038_ = lean_box(v___x_4037_);
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
return v___x_4039_;
}
else
{
lean_object* v_one_4040_; lean_object* v_n_4041_; 
v_one_4040_ = lean_unsigned_to_nat(1u);
v_n_4041_ = lean_nat_sub(v_x_3983_, v_one_4040_);
lean_dec(v_x_3983_);
v_x_3982_ = v_body_4034_;
v_x_3983_ = v_n_4041_;
goto _start;
}
}
default: 
{
uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
lean_dec(v_x_3983_);
lean_dec_ref(v_x_3982_);
v___x_4043_ = 2;
v___x_4044_ = lean_box(v___x_4043_);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
return v___x_4045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4046_, lean_object* v_x_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4046_, v_x_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
switch(lean_obj_tag(v_x_4054_))
{
case 1:
{
lean_object* v_fvarId_4060_; lean_object* v___x_4061_; 
v_fvarId_4060_ = lean_ctor_get(v_x_4054_, 0);
lean_inc(v_fvarId_4060_);
lean_dec_ref_known(v_x_4054_, 1);
v___x_4061_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4060_, v_a_4055_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v___x_4063_ = lean_unsigned_to_nat(0u);
v___x_4064_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4062_, v___x_4063_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4064_;
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
v_a_4065_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4061_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4061_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4073_; lean_object* v___x_4074_; 
v_mvarId_4073_ = lean_ctor_get(v_x_4054_, 0);
lean_inc(v_mvarId_4073_);
lean_dec_ref_known(v_x_4054_, 1);
v___x_4074_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4073_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v___x_4076_ = lean_unsigned_to_nat(0u);
v___x_4077_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4075_, v___x_4076_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4077_;
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
v_a_4078_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4074_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4074_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
case 3:
{
uint8_t v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
lean_dec_ref_known(v_x_4054_, 1);
v___x_4086_ = 0;
v___x_4087_ = lean_box(v___x_4086_);
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
case 4:
{
lean_object* v_declName_4089_; lean_object* v_us_4090_; lean_object* v___x_4091_; 
v_declName_4089_ = lean_ctor_get(v_x_4054_, 0);
lean_inc(v_declName_4089_);
v_us_4090_ = lean_ctor_get(v_x_4054_, 1);
lean_inc(v_us_4090_);
lean_dec_ref_known(v_x_4054_, 2);
v___x_4091_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4089_, v_us_4090_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4091_, 1);
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4094_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4092_, v___x_4093_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4094_;
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
v_a_4095_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4091_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4091_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
case 5:
{
lean_object* v_fn_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v_fn_4103_ = lean_ctor_get(v_x_4054_, 0);
lean_inc_ref(v_fn_4103_);
lean_dec_ref_known(v_x_4054_, 2);
v___x_4104_ = lean_unsigned_to_nat(1u);
v___x_4105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4103_, v___x_4104_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4105_;
}
case 6:
{
uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_dec_ref_known(v_x_4054_, 3);
v___x_4106_ = 0;
v___x_4107_ = lean_box(v___x_4106_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
return v___x_4108_;
}
case 7:
{
lean_object* v_body_4109_; 
v_body_4109_ = lean_ctor_get(v_x_4054_, 2);
lean_inc_ref(v_body_4109_);
lean_dec_ref_known(v_x_4054_, 3);
v_x_4054_ = v_body_4109_;
goto _start;
}
case 8:
{
lean_object* v_body_4111_; 
v_body_4111_ = lean_ctor_get(v_x_4054_, 3);
lean_inc_ref(v_body_4111_);
lean_dec_ref_known(v_x_4054_, 4);
v_x_4054_ = v_body_4111_;
goto _start;
}
case 9:
{
uint8_t v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_dec_ref_known(v_x_4054_, 1);
v___x_4113_ = 0;
v___x_4114_ = lean_box(v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
case 10:
{
lean_object* v_expr_4116_; 
v_expr_4116_ = lean_ctor_get(v_x_4054_, 1);
lean_inc_ref(v_expr_4116_);
lean_dec_ref_known(v_x_4054_, 2);
v_x_4054_ = v_expr_4116_;
goto _start;
}
default: 
{
uint8_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_dec_ref(v_x_4054_);
v___x_4118_ = 2;
v___x_4119_ = lean_box(v___x_4118_);
v___x_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
return v___x_4120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_Meta_isPropQuick(v_x_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_);
lean_dec(v_a_4125_);
lean_dec_ref(v_a_4124_);
lean_dec(v_a_4123_);
lean_dec_ref(v_a_4122_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v___x_4134_; 
lean_inc_ref(v_e_4128_);
v___x_4134_ = l_Lean_Meta_isPropQuick(v_e_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4191_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4191_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4191_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
uint8_t v___x_4139_; 
v___x_4139_ = lean_unbox(v_a_4135_);
lean_dec(v_a_4135_);
switch(v___x_4139_)
{
case 0:
{
uint8_t v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
lean_dec_ref(v_e_4128_);
v___x_4140_ = 0;
v___x_4141_ = lean_box(v___x_4140_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v___x_4141_);
v___x_4143_ = v___x_4137_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
case 1:
{
uint8_t v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
lean_dec_ref(v_e_4128_);
v___x_4145_ = 1;
v___x_4146_ = lean_box(v___x_4145_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v___x_4146_);
v___x_4148_ = v___x_4137_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
default: 
{
lean_object* v___x_4150_; 
lean_del_object(v___x_4137_);
lean_inc(v_a_4132_);
lean_inc_ref(v_a_4131_);
lean_inc(v_a_4130_);
lean_inc_ref(v_a_4129_);
v___x_4150_ = lean_infer_type(v_e_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4152_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v___x_4152_ = l_Lean_Meta_whnfD(v_a_4151_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4174_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4174_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4174_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
if (lean_obj_tag(v_a_4153_) == 3)
{
lean_object* v_u_4157_; lean_object* v___x_4158_; lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4168_; 
lean_del_object(v___x_4155_);
v_u_4157_ = lean_ctor_get(v_a_4153_, 0);
lean_inc(v_u_4157_);
lean_dec_ref_known(v_a_4153_, 1);
v___x_4158_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4157_, v_a_4130_);
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4168_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4168_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
uint8_t v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4163_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4159_);
lean_dec(v_a_4159_);
v___x_4164_ = lean_box(v___x_4163_);
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4164_);
v___x_4166_ = v___x_4161_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
else
{
uint8_t v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
lean_dec(v_a_4153_);
v___x_4169_ = 0;
v___x_4170_ = lean_box(v___x_4169_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v___x_4170_);
v___x_4172_ = v___x_4155_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4175_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4152_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4152_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4150_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4150_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec_ref(v_e_4128_);
v_a_4192_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4134_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4134_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_Meta_isProp(v_e_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
lean_dec(v_a_4204_);
lean_dec_ref(v_a_4203_);
lean_dec(v_a_4202_);
lean_dec_ref(v_a_4201_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4207_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = lean_obj_tag_nat(v_x_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4209_);
lean_dec(v_x_4209_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4211_, lean_object* v_k_4212_){
_start:
{
if (lean_obj_tag(v_t_4211_) == 3)
{
lean_object* v_idx_4213_; lean_object* v_numArgs_4214_; lean_object* v___x_4215_; 
v_idx_4213_ = lean_ctor_get(v_t_4211_, 0);
lean_inc(v_idx_4213_);
v_numArgs_4214_ = lean_ctor_get(v_t_4211_, 1);
lean_inc(v_numArgs_4214_);
lean_dec_ref_known(v_t_4211_, 2);
v___x_4215_ = lean_apply_2(v_k_4212_, v_idx_4213_, v_numArgs_4214_);
return v___x_4215_;
}
else
{
lean_dec(v_t_4211_);
return v_k_4212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4216_, lean_object* v_ctorIdx_4217_, lean_object* v_t_4218_, lean_object* v_h_4219_, lean_object* v_k_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4218_, v_k_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4222_, lean_object* v_ctorIdx_4223_, lean_object* v_t_4224_, lean_object* v_h_4225_, lean_object* v_k_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4222_, v_ctorIdx_4223_, v_t_4224_, v_h_4225_, v_k_4226_);
lean_dec(v_ctorIdx_4223_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4228_, lean_object* v_false_4229_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4228_, v_false_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4231_, lean_object* v_t_4232_, lean_object* v_h_4233_, lean_object* v_false_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4232_, v_false_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4236_, lean_object* v_true_4237_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4236_, v_true_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4239_, lean_object* v_t_4240_, lean_object* v_h_4241_, lean_object* v_true_4242_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4240_, v_true_4242_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4244_, lean_object* v_undef_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4244_, v_undef_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4247_, lean_object* v_t_4248_, lean_object* v_h_4249_, lean_object* v_undef_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4248_, v_undef_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4252_, lean_object* v_bvar_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4252_, v_bvar_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4255_, lean_object* v_t_4256_, lean_object* v_h_4257_, lean_object* v_bvar_4258_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4256_, v_bvar_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4260_){
_start:
{
switch(v_x_4260_)
{
case 0:
{
lean_object* v___x_4261_; 
v___x_4261_ = lean_box(0);
return v___x_4261_;
}
case 1:
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_box(1);
return v___x_4262_;
}
default: 
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_box(2);
return v___x_4263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4264_){
_start:
{
uint8_t v_x_25__boxed_4265_; lean_object* v_res_4266_; 
v_x_25__boxed_4265_ = lean_unbox(v_x_4264_);
v_res_4266_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4265_);
return v_res_4266_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4267_){
_start:
{
switch(lean_obj_tag(v_x_4267_))
{
case 0:
{
uint8_t v___x_4268_; 
v___x_4268_ = 0;
return v___x_4268_;
}
case 1:
{
uint8_t v___x_4269_; 
v___x_4269_ = 1;
return v___x_4269_;
}
default: 
{
uint8_t v___x_4270_; 
v___x_4270_ = 2;
return v___x_4270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4271_){
_start:
{
uint8_t v_res_4272_; lean_object* v_r_4273_; 
v_res_4272_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4271_);
lean_dec(v_x_4271_);
v_r_4273_ = lean_box(v_res_4272_);
return v_r_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4275_, lean_object* v_numArgs_4276_){
_start:
{
switch(lean_obj_tag(v_e_4275_))
{
case 3:
{
lean_object* v_u_4277_; lean_object* v___x_4278_; uint8_t v___x_4279_; 
v_u_4277_ = lean_ctor_get(v_e_4275_, 0);
v___x_4278_ = lean_unsigned_to_nat(0u);
v___x_4279_ = lean_nat_dec_eq(v_numArgs_4276_, v___x_4278_);
lean_dec(v_numArgs_4276_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; 
v___x_4280_ = lean_box(2);
return v___x_4280_;
}
else
{
uint8_t v___x_4281_; 
v___x_4281_ = l_Lean_Level_isNeverZero(v_u_4277_);
if (v___x_4281_ == 0)
{
uint8_t v___x_4282_; 
v___x_4282_ = l_Lean_Level_isZero(v_u_4277_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; 
v___x_4283_ = lean_box(2);
return v___x_4283_;
}
else
{
lean_object* v___x_4284_; 
v___x_4284_ = lean_box(1);
return v___x_4284_;
}
}
else
{
lean_object* v___x_4285_; 
v___x_4285_ = lean_box(0);
return v___x_4285_;
}
}
}
case 7:
{
lean_object* v_body_4286_; lean_object* v_zero_4287_; uint8_t v_isZero_4288_; 
v_body_4286_ = lean_ctor_get(v_e_4275_, 2);
v_zero_4287_ = lean_unsigned_to_nat(0u);
v_isZero_4288_ = lean_nat_dec_eq(v_numArgs_4276_, v_zero_4287_);
if (v_isZero_4288_ == 0)
{
lean_object* v_one_4289_; lean_object* v_n_4290_; 
v_one_4289_ = lean_unsigned_to_nat(1u);
v_n_4290_ = lean_nat_sub(v_numArgs_4276_, v_one_4289_);
lean_dec(v_numArgs_4276_);
v_e_4275_ = v_body_4286_;
v_numArgs_4276_ = v_n_4290_;
goto _start;
}
else
{
lean_object* v___x_4292_; 
lean_dec(v_numArgs_4276_);
v___x_4292_ = lean_box(2);
return v___x_4292_;
}
}
case 10:
{
lean_object* v_expr_4293_; 
v_expr_4293_ = lean_ctor_get(v_e_4275_, 1);
v_e_4275_ = v_expr_4293_;
goto _start;
}
case 5:
{
lean_object* v_fn_4295_; 
v_fn_4295_ = lean_ctor_get(v_e_4275_, 0);
if (lean_obj_tag(v_fn_4295_) == 4)
{
lean_object* v_declName_4296_; 
v_declName_4296_ = lean_ctor_get(v_fn_4295_, 0);
if (lean_obj_tag(v_declName_4296_) == 1)
{
lean_object* v_pre_4297_; 
v_pre_4297_ = lean_ctor_get(v_declName_4296_, 0);
if (lean_obj_tag(v_pre_4297_) == 0)
{
lean_object* v_arg_4298_; lean_object* v_str_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v_arg_4298_ = lean_ctor_get(v_e_4275_, 1);
v_str_4299_ = lean_ctor_get(v_declName_4296_, 1);
v___x_4300_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4301_ = lean_string_dec_eq(v_str_4299_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; 
lean_dec(v_numArgs_4276_);
v___x_4302_ = lean_box(2);
return v___x_4302_;
}
else
{
v_e_4275_ = v_arg_4298_;
goto _start;
}
}
else
{
lean_object* v___x_4304_; 
lean_dec(v_numArgs_4276_);
v___x_4304_ = lean_box(2);
return v___x_4304_;
}
}
else
{
lean_object* v___x_4305_; 
lean_dec(v_numArgs_4276_);
v___x_4305_ = lean_box(2);
return v___x_4305_;
}
}
else
{
lean_object* v___x_4306_; 
lean_dec(v_numArgs_4276_);
v___x_4306_ = lean_box(2);
return v___x_4306_;
}
}
default: 
{
lean_object* v___x_4307_; 
lean_dec(v_numArgs_4276_);
v___x_4307_ = lean_box(2);
return v___x_4307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4308_, lean_object* v_numArgs_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4308_, v_numArgs_4309_);
lean_dec_ref(v_e_4308_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4311_, lean_object* v_binderType_4312_){
_start:
{
if (lean_obj_tag(v_r_4311_) == 3)
{
lean_object* v_idx_4313_; lean_object* v_numArgs_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4326_; 
v_idx_4313_ = lean_ctor_get(v_r_4311_, 0);
v_numArgs_4314_ = lean_ctor_get(v_r_4311_, 1);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_r_4311_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4316_ = v_r_4311_;
v_isShared_4317_ = v_isSharedCheck_4326_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_numArgs_4314_);
lean_inc(v_idx_4313_);
lean_dec(v_r_4311_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4326_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v_zero_4318_; uint8_t v_isZero_4319_; 
v_zero_4318_ = lean_unsigned_to_nat(0u);
v_isZero_4319_ = lean_nat_dec_eq(v_idx_4313_, v_zero_4318_);
if (v_isZero_4319_ == 1)
{
lean_object* v___x_4320_; 
lean_del_object(v___x_4316_);
lean_dec(v_idx_4313_);
v___x_4320_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4312_, v_numArgs_4314_);
return v___x_4320_;
}
else
{
lean_object* v_one_4321_; lean_object* v_n_4322_; lean_object* v___x_4324_; 
v_one_4321_ = lean_unsigned_to_nat(1u);
v_n_4322_ = lean_nat_sub(v_idx_4313_, v_one_4321_);
lean_dec(v_idx_4313_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v_n_4322_);
v___x_4324_ = v___x_4316_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_n_4322_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_numArgs_4314_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
else
{
return v_r_4311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4327_, lean_object* v_binderType_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4327_, v_binderType_4328_);
lean_dec_ref(v_binderType_4328_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4330_, lean_object* v_x_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_type_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; 
switch(lean_obj_tag(v_x_4330_))
{
case 7:
{
lean_object* v_binderType_4370_; lean_object* v_body_4371_; lean_object* v_zero_4372_; uint8_t v_isZero_4373_; 
v_binderType_4370_ = lean_ctor_get(v_x_4330_, 1);
v_body_4371_ = lean_ctor_get(v_x_4330_, 2);
v_zero_4372_ = lean_unsigned_to_nat(0u);
v_isZero_4373_ = lean_nat_dec_eq(v_x_4331_, v_zero_4372_);
if (v_isZero_4373_ == 1)
{
v_type_4338_ = v_x_4330_;
v___y_4339_ = v_a_4332_;
v___y_4340_ = v_a_4333_;
v___y_4341_ = v_a_4334_;
v___y_4342_ = v_a_4335_;
goto v___jp_4337_;
}
else
{
lean_object* v_one_4374_; lean_object* v_n_4375_; lean_object* v___x_4376_; 
lean_inc_ref(v_body_4371_);
lean_inc_ref(v_binderType_4370_);
lean_dec_ref_known(v_x_4330_, 3);
v_one_4374_ = lean_unsigned_to_nat(1u);
v_n_4375_ = lean_nat_sub(v_x_4331_, v_one_4374_);
v___x_4376_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4371_, v_n_4375_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_);
lean_dec(v_n_4375_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4385_; 
v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4379_ = v___x_4376_;
v_isShared_4380_ = v_isSharedCheck_4385_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4376_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4385_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; lean_object* v___x_4383_; 
v___x_4381_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4377_, v_binderType_4370_);
lean_dec_ref(v_binderType_4370_);
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4381_);
v___x_4383_ = v___x_4379_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
else
{
lean_dec_ref(v_binderType_4370_);
return v___x_4376_;
}
}
}
case 8:
{
lean_object* v_type_4386_; lean_object* v_body_4387_; lean_object* v___x_4388_; 
v_type_4386_ = lean_ctor_get(v_x_4330_, 1);
lean_inc_ref(v_type_4386_);
v_body_4387_ = lean_ctor_get(v_x_4330_, 3);
lean_inc_ref(v_body_4387_);
lean_dec_ref_known(v_x_4330_, 4);
v___x_4388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4387_, v_x_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4397_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4391_ = v___x_4388_;
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4388_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4393_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4389_, v_type_4386_);
lean_dec_ref(v_type_4386_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 0, v___x_4393_);
v___x_4395_ = v___x_4391_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
else
{
lean_dec_ref(v_type_4386_);
return v___x_4388_;
}
}
case 10:
{
lean_object* v_expr_4398_; 
v_expr_4398_ = lean_ctor_get(v_x_4330_, 1);
lean_inc_ref(v_expr_4398_);
lean_dec_ref_known(v_x_4330_, 2);
v_x_4330_ = v_expr_4398_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4400_; lean_object* v___x_4401_; uint8_t v___x_4402_; 
v_deBruijnIndex_4400_ = lean_ctor_get(v_x_4330_, 0);
lean_inc(v_deBruijnIndex_4400_);
lean_dec_ref_known(v_x_4330_, 1);
v___x_4401_ = lean_unsigned_to_nat(0u);
v___x_4402_ = lean_nat_dec_eq(v_x_4331_, v___x_4401_);
if (v___x_4402_ == 0)
{
lean_dec(v_deBruijnIndex_4400_);
goto v___jp_4367_;
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4403_, 0, v_deBruijnIndex_4400_);
lean_ctor_set(v___x_4403_, 1, v___x_4401_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
}
default: 
{
lean_object* v___x_4405_; uint8_t v___x_4406_; 
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = lean_nat_dec_eq(v_x_4331_, v___x_4405_);
if (v___x_4406_ == 0)
{
lean_dec_ref(v_x_4330_);
goto v___jp_4367_;
}
else
{
v_type_4338_ = v_x_4330_;
v___y_4339_ = v_a_4332_;
v___y_4340_ = v_a_4333_;
v___y_4341_ = v_a_4334_;
v___y_4342_ = v_a_4335_;
goto v___jp_4337_;
}
}
}
v___jp_4337_:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_Lean_Expr_getAppFn(v_type_4338_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_deBruijnIndex_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v_deBruijnIndex_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_deBruijnIndex_4344_);
lean_dec_ref_known(v___x_4343_, 1);
v___x_4345_ = l_Lean_Expr_getAppNumArgs(v_type_4338_);
lean_dec_ref(v_type_4338_);
v___x_4346_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4346_, 0, v_deBruijnIndex_4344_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
return v___x_4347_;
}
else
{
lean_object* v___x_4348_; 
lean_dec_ref(v___x_4343_);
v___x_4348_ = l_Lean_Meta_isPropQuick(v_type_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4358_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4351_ = v___x_4348_;
v_isShared_4352_ = v_isSharedCheck_4358_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4348_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4358_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
uint8_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4353_ = lean_unbox(v_a_4349_);
lean_dec(v_a_4349_);
v___x_4354_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4353_);
if (v_isShared_4352_ == 0)
{
lean_ctor_set(v___x_4351_, 0, v___x_4354_);
v___x_4356_ = v___x_4351_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
v_a_4359_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4348_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4348_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
v___jp_4367_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = lean_box(2);
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
return v___x_4369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4407_, lean_object* v_x_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4407_, v_x_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_);
lean_dec(v_a_4412_);
lean_dec_ref(v_a_4411_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_x_4408_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4415_, lean_object* v_n_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4415_, v_n_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4432_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4432_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4432_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
uint8_t v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4430_; 
v___x_4427_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4423_);
lean_dec(v_a_4423_);
v___x_4428_ = lean_box(v___x_4427_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 0, v___x_4428_);
v___x_4430_ = v___x_4425_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
v_a_4433_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4422_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4422_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4441_, lean_object* v_n_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4441_, v_n_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_n_4442_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
switch(lean_obj_tag(v_x_4449_))
{
case 1:
{
lean_object* v_fvarId_4455_; lean_object* v___x_4456_; 
v_fvarId_4455_ = lean_ctor_get(v_x_4449_, 0);
lean_inc(v_fvarId_4455_);
lean_dec_ref_known(v_x_4449_, 1);
v___x_4456_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4455_, v_a_4450_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref_known(v___x_4456_, 1);
v___x_4458_ = lean_unsigned_to_nat(0u);
v___x_4459_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4457_, v___x_4458_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4459_;
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
v_a_4460_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4456_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4456_);
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
case 2:
{
lean_object* v_mvarId_4468_; lean_object* v___x_4469_; 
v_mvarId_4468_ = lean_ctor_get(v_x_4449_, 0);
lean_inc(v_mvarId_4468_);
lean_dec_ref_known(v_x_4449_, 1);
v___x_4469_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4468_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4470_);
lean_dec_ref_known(v___x_4469_, 1);
v___x_4471_ = lean_unsigned_to_nat(0u);
v___x_4472_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4470_, v___x_4471_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4472_;
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
v_a_4473_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4469_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4469_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
case 3:
{
uint8_t v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
lean_dec_ref_known(v_x_4449_, 1);
v___x_4481_ = 0;
v___x_4482_ = lean_box(v___x_4481_);
v___x_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
return v___x_4483_;
}
case 4:
{
lean_object* v_declName_4484_; lean_object* v_us_4485_; lean_object* v___x_4486_; 
v_declName_4484_ = lean_ctor_get(v_x_4449_, 0);
lean_inc(v_declName_4484_);
v_us_4485_ = lean_ctor_get(v_x_4449_, 1);
lean_inc(v_us_4485_);
lean_dec_ref_known(v_x_4449_, 2);
v___x_4486_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4484_, v_us_4485_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___x_4488_ = lean_unsigned_to_nat(0u);
v___x_4489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4487_, v___x_4488_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4489_;
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
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
v_fn_4498_ = lean_ctor_get(v_x_4449_, 0);
lean_inc_ref(v_fn_4498_);
lean_dec_ref_known(v_x_4449_, 2);
v___x_4499_ = lean_unsigned_to_nat(1u);
v___x_4500_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4498_, v___x_4499_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
return v___x_4500_;
}
case 6:
{
lean_object* v_body_4501_; 
v_body_4501_ = lean_ctor_get(v_x_4449_, 2);
lean_inc_ref(v_body_4501_);
lean_dec_ref_known(v_x_4449_, 3);
v_x_4449_ = v_body_4501_;
goto _start;
}
case 7:
{
uint8_t v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
lean_dec_ref_known(v_x_4449_, 3);
v___x_4503_ = 0;
v___x_4504_ = lean_box(v___x_4503_);
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
return v___x_4505_;
}
case 8:
{
lean_object* v_body_4506_; 
v_body_4506_ = lean_ctor_get(v_x_4449_, 3);
lean_inc_ref(v_body_4506_);
lean_dec_ref_known(v_x_4449_, 4);
v_x_4449_ = v_body_4506_;
goto _start;
}
case 9:
{
uint8_t v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec_ref_known(v_x_4449_, 1);
v___x_4508_ = 0;
v___x_4509_ = lean_box(v___x_4508_);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
case 10:
{
lean_object* v_expr_4511_; 
v_expr_4511_ = lean_ctor_get(v_x_4449_, 1);
lean_inc_ref(v_expr_4511_);
lean_dec_ref_known(v_x_4449_, 2);
v_x_4449_ = v_expr_4511_;
goto _start;
}
default: 
{
uint8_t v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
lean_dec_ref(v_x_4449_);
v___x_4513_ = 2;
v___x_4514_ = lean_box(v___x_4513_);
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
return v___x_4515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4516_, lean_object* v_x_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_){
_start:
{
switch(lean_obj_tag(v_x_4516_))
{
case 4:
{
lean_object* v_declName_4523_; lean_object* v_us_4524_; lean_object* v___x_4525_; 
v_declName_4523_ = lean_ctor_get(v_x_4516_, 0);
lean_inc(v_declName_4523_);
v_us_4524_ = lean_ctor_get(v_x_4516_, 1);
lean_inc(v_us_4524_);
lean_dec_ref_known(v_x_4516_, 2);
v___x_4525_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4523_, v_us_4524_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v___x_4527_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4525_, 1);
v___x_4527_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4526_, v_x_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_x_4517_);
return v___x_4527_;
}
else
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
lean_dec(v_x_4517_);
v_a_4528_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4525_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4525_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4536_; lean_object* v___x_4537_; 
v_fvarId_4536_ = lean_ctor_get(v_x_4516_, 0);
lean_inc(v_fvarId_4536_);
lean_dec_ref_known(v_x_4516_, 1);
v___x_4537_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4536_, v_a_4518_, v_a_4520_, v_a_4521_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4539_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v___x_4539_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4538_, v_x_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_x_4517_);
return v___x_4539_;
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec(v_x_4517_);
v_a_4540_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4537_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4537_);
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
v_mvarId_4548_ = lean_ctor_get(v_x_4516_, 0);
lean_inc(v_mvarId_4548_);
lean_dec_ref_known(v_x_4516_, 1);
v___x_4549_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4548_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4551_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v___x_4551_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4550_, v_x_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_x_4517_);
return v___x_4551_;
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_x_4517_);
v_a_4552_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4549_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4549_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
case 5:
{
lean_object* v_fn_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v_fn_4560_ = lean_ctor_get(v_x_4516_, 0);
lean_inc_ref(v_fn_4560_);
lean_dec_ref_known(v_x_4516_, 2);
v___x_4561_ = lean_unsigned_to_nat(1u);
v___x_4562_ = lean_nat_add(v_x_4517_, v___x_4561_);
lean_dec(v_x_4517_);
v_x_4516_ = v_fn_4560_;
v_x_4517_ = v___x_4562_;
goto _start;
}
case 10:
{
lean_object* v_expr_4564_; 
v_expr_4564_ = lean_ctor_get(v_x_4516_, 1);
lean_inc_ref(v_expr_4564_);
lean_dec_ref_known(v_x_4516_, 2);
v_x_4516_ = v_expr_4564_;
goto _start;
}
case 8:
{
lean_object* v_body_4566_; 
v_body_4566_ = lean_ctor_get(v_x_4516_, 3);
lean_inc_ref(v_body_4566_);
lean_dec_ref_known(v_x_4516_, 4);
v_x_4516_ = v_body_4566_;
goto _start;
}
case 6:
{
lean_object* v_body_4568_; lean_object* v_zero_4569_; uint8_t v_isZero_4570_; 
v_body_4568_ = lean_ctor_get(v_x_4516_, 2);
lean_inc_ref(v_body_4568_);
lean_dec_ref_known(v_x_4516_, 3);
v_zero_4569_ = lean_unsigned_to_nat(0u);
v_isZero_4570_ = lean_nat_dec_eq(v_x_4517_, v_zero_4569_);
if (v_isZero_4570_ == 1)
{
lean_object* v___x_4571_; 
lean_dec(v_x_4517_);
v___x_4571_ = l_Lean_Meta_isProofQuick(v_body_4568_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
return v___x_4571_;
}
else
{
lean_object* v_one_4572_; lean_object* v_n_4573_; 
v_one_4572_ = lean_unsigned_to_nat(1u);
v_n_4573_ = lean_nat_sub(v_x_4517_, v_one_4572_);
lean_dec(v_x_4517_);
v_x_4516_ = v_body_4568_;
v_x_4517_ = v_n_4573_;
goto _start;
}
}
default: 
{
uint8_t v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
lean_dec(v_x_4517_);
lean_dec_ref(v_x_4516_);
v___x_4575_ = 2;
v___x_4576_ = lean_box(v___x_4575_);
v___x_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
return v___x_4577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4578_, lean_object* v_x_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4578_, v_x_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
lean_dec(v_a_4581_);
lean_dec_ref(v_a_4580_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Lean_Meta_isProofQuick(v_x_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v___x_4599_; 
lean_inc_ref(v_e_4593_);
v___x_4599_ = l_Lean_Meta_isProofQuick(v_e_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4626_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4602_ = v___x_4599_;
v_isShared_4603_ = v_isSharedCheck_4626_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4599_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4626_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
uint8_t v___x_4604_; 
v___x_4604_ = lean_unbox(v_a_4600_);
lean_dec(v_a_4600_);
switch(v___x_4604_)
{
case 0:
{
uint8_t v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4608_; 
lean_dec_ref(v_e_4593_);
v___x_4605_ = 0;
v___x_4606_ = lean_box(v___x_4605_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4606_);
v___x_4608_ = v___x_4602_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
case 1:
{
uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4613_; 
lean_dec_ref(v_e_4593_);
v___x_4610_ = 1;
v___x_4611_ = lean_box(v___x_4610_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4611_);
v___x_4613_ = v___x_4602_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4611_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
default: 
{
lean_object* v___x_4615_; 
lean_del_object(v___x_4602_);
lean_inc(v_a_4597_);
lean_inc_ref(v_a_4596_);
lean_inc(v_a_4595_);
lean_inc_ref(v_a_4594_);
v___x_4615_ = lean_infer_type(v_e_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4617_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc(v_a_4616_);
lean_dec_ref_known(v___x_4615_, 1);
v___x_4617_ = l_Lean_Meta_isProp(v_a_4616_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
return v___x_4617_;
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
v_a_4618_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4615_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4615_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_dec_ref(v_e_4593_);
v_a_4627_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4599_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4599_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_Meta_isProof(v_e_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_);
lean_dec(v_a_4639_);
lean_dec_ref(v_a_4638_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4642_, lean_object* v_x_4643_){
_start:
{
switch(lean_obj_tag(v_x_4642_))
{
case 3:
{
lean_object* v___x_4649_; uint8_t v___x_4650_; 
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = lean_nat_dec_eq(v_x_4643_, v___x_4649_);
lean_dec(v_x_4643_);
if (v___x_4650_ == 0)
{
goto v___jp_4645_;
}
else
{
uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4651_ = 1;
v___x_4652_ = lean_box(v___x_4651_);
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
return v___x_4653_;
}
}
case 7:
{
lean_object* v_body_4654_; lean_object* v_zero_4655_; uint8_t v_isZero_4656_; 
v_body_4654_ = lean_ctor_get(v_x_4642_, 2);
v_zero_4655_ = lean_unsigned_to_nat(0u);
v_isZero_4656_ = lean_nat_dec_eq(v_x_4643_, v_zero_4655_);
if (v_isZero_4656_ == 1)
{
uint8_t v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
lean_dec(v_x_4643_);
v___x_4657_ = 0;
v___x_4658_ = lean_box(v___x_4657_);
v___x_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
return v___x_4659_;
}
else
{
lean_object* v_one_4660_; lean_object* v_n_4661_; 
v_one_4660_ = lean_unsigned_to_nat(1u);
v_n_4661_ = lean_nat_sub(v_x_4643_, v_one_4660_);
lean_dec(v_x_4643_);
v_x_4642_ = v_body_4654_;
v_x_4643_ = v_n_4661_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4663_; 
v_body_4663_ = lean_ctor_get(v_x_4642_, 3);
v_x_4642_ = v_body_4663_;
goto _start;
}
case 10:
{
lean_object* v_expr_4665_; 
v_expr_4665_ = lean_ctor_get(v_x_4642_, 1);
v_x_4642_ = v_expr_4665_;
goto _start;
}
default: 
{
lean_dec(v_x_4643_);
goto v___jp_4645_;
}
}
v___jp_4645_:
{
uint8_t v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = 2;
v___x_4647_ = lean_box(v___x_4646_);
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4667_, lean_object* v_x_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4667_, v_x_4668_);
lean_dec_ref(v_x_4667_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4671_, lean_object* v_x_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_){
_start:
{
lean_object* v___x_4678_; 
v___x_4678_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4671_, v_x_4672_);
return v___x_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4679_, lean_object* v_x_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4679_, v_x_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec_ref(v_x_4679_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4687_, lean_object* v_x_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_){
_start:
{
switch(lean_obj_tag(v_x_4687_))
{
case 4:
{
lean_object* v_declName_4694_; lean_object* v_us_4695_; lean_object* v___x_4696_; 
v_declName_4694_ = lean_ctor_get(v_x_4687_, 0);
lean_inc(v_declName_4694_);
v_us_4695_ = lean_ctor_get(v_x_4687_, 1);
lean_inc(v_us_4695_);
lean_dec_ref_known(v_x_4687_, 2);
v___x_4696_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4694_, v_us_4695_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4698_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
lean_inc(v_a_4697_);
lean_dec_ref_known(v___x_4696_, 1);
v___x_4698_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4697_, v_x_4688_);
lean_dec(v_a_4697_);
return v___x_4698_;
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
lean_dec(v_x_4688_);
v_a_4699_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4696_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4696_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4707_; lean_object* v___x_4708_; 
v_fvarId_4707_ = lean_ctor_get(v_x_4687_, 0);
lean_inc(v_fvarId_4707_);
lean_dec_ref_known(v_x_4687_, 1);
v___x_4708_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4707_, v_a_4689_, v_a_4691_, v_a_4692_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4710_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref_known(v___x_4708_, 1);
v___x_4710_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4709_, v_x_4688_);
lean_dec(v_a_4709_);
return v___x_4710_;
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v_x_4688_);
v_a_4711_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4708_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4708_);
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
case 2:
{
lean_object* v_mvarId_4719_; lean_object* v___x_4720_; 
v_mvarId_4719_ = lean_ctor_get(v_x_4687_, 0);
lean_inc(v_mvarId_4719_);
lean_dec_ref_known(v_x_4687_, 1);
v___x_4720_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4719_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4722_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v___x_4722_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4721_, v_x_4688_);
lean_dec(v_a_4721_);
return v___x_4722_;
}
else
{
lean_object* v_a_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4730_; 
lean_dec(v_x_4688_);
v_a_4723_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4725_ = v___x_4720_;
v_isShared_4726_ = v_isSharedCheck_4730_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_a_4723_);
lean_dec(v___x_4720_);
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
case 5:
{
lean_object* v_fn_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v_fn_4731_ = lean_ctor_get(v_x_4687_, 0);
lean_inc_ref(v_fn_4731_);
lean_dec_ref_known(v_x_4687_, 2);
v___x_4732_ = lean_unsigned_to_nat(1u);
v___x_4733_ = lean_nat_add(v_x_4688_, v___x_4732_);
lean_dec(v_x_4688_);
v_x_4687_ = v_fn_4731_;
v_x_4688_ = v___x_4733_;
goto _start;
}
case 10:
{
lean_object* v_expr_4735_; 
v_expr_4735_ = lean_ctor_get(v_x_4687_, 1);
lean_inc_ref(v_expr_4735_);
lean_dec_ref_known(v_x_4687_, 2);
v_x_4687_ = v_expr_4735_;
goto _start;
}
case 8:
{
lean_object* v_body_4737_; 
v_body_4737_ = lean_ctor_get(v_x_4687_, 3);
lean_inc_ref(v_body_4737_);
lean_dec_ref_known(v_x_4687_, 4);
v_x_4687_ = v_body_4737_;
goto _start;
}
case 6:
{
lean_object* v_body_4739_; lean_object* v_zero_4740_; uint8_t v_isZero_4741_; 
v_body_4739_ = lean_ctor_get(v_x_4687_, 2);
lean_inc_ref(v_body_4739_);
lean_dec_ref_known(v_x_4687_, 3);
v_zero_4740_ = lean_unsigned_to_nat(0u);
v_isZero_4741_ = lean_nat_dec_eq(v_x_4688_, v_zero_4740_);
if (v_isZero_4741_ == 1)
{
uint8_t v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
lean_dec_ref(v_body_4739_);
lean_dec(v_x_4688_);
v___x_4742_ = 0;
v___x_4743_ = lean_box(v___x_4742_);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
else
{
lean_object* v_one_4745_; lean_object* v_n_4746_; 
v_one_4745_ = lean_unsigned_to_nat(1u);
v_n_4746_ = lean_nat_sub(v_x_4688_, v_one_4745_);
lean_dec(v_x_4688_);
v_x_4687_ = v_body_4739_;
v_x_4688_ = v_n_4746_;
goto _start;
}
}
default: 
{
uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
lean_dec(v_x_4688_);
lean_dec_ref(v_x_4687_);
v___x_4748_ = 2;
v___x_4749_ = lean_box(v___x_4748_);
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
return v___x_4750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4751_, lean_object* v_x_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4751_, v_x_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_){
_start:
{
switch(lean_obj_tag(v_x_4759_))
{
case 1:
{
lean_object* v_fvarId_4765_; lean_object* v___x_4766_; 
v_fvarId_4765_ = lean_ctor_get(v_x_4759_, 0);
lean_inc(v_fvarId_4765_);
lean_dec_ref_known(v_x_4759_, 1);
v___x_4766_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4765_, v_a_4760_, v_a_4762_, v_a_4763_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_a_4767_);
lean_dec_ref_known(v___x_4766_, 1);
v___x_4768_ = lean_unsigned_to_nat(0u);
v___x_4769_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4767_, v___x_4768_);
lean_dec(v_a_4767_);
return v___x_4769_;
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
v_a_4770_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4766_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4766_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4778_; lean_object* v___x_4779_; 
v_mvarId_4778_ = lean_ctor_get(v_x_4759_, 0);
lean_inc(v_mvarId_4778_);
lean_dec_ref_known(v_x_4759_, 1);
v___x_4779_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4778_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref_known(v___x_4779_, 1);
v___x_4781_ = lean_unsigned_to_nat(0u);
v___x_4782_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4780_, v___x_4781_);
lean_dec(v_a_4780_);
return v___x_4782_;
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
v_a_4783_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4779_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4779_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
case 3:
{
uint8_t v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
lean_dec_ref_known(v_x_4759_, 1);
v___x_4791_ = 1;
v___x_4792_ = lean_box(v___x_4791_);
v___x_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
return v___x_4793_;
}
case 4:
{
lean_object* v_declName_4794_; lean_object* v_us_4795_; lean_object* v___x_4796_; 
v_declName_4794_ = lean_ctor_get(v_x_4759_, 0);
lean_inc(v_declName_4794_);
v_us_4795_ = lean_ctor_get(v_x_4759_, 1);
lean_inc(v_us_4795_);
lean_dec_ref_known(v_x_4759_, 2);
v___x_4796_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4794_, v_us_4795_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
lean_inc(v_a_4797_);
lean_dec_ref_known(v___x_4796_, 1);
v___x_4798_ = lean_unsigned_to_nat(0u);
v___x_4799_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4797_, v___x_4798_);
lean_dec(v_a_4797_);
return v___x_4799_;
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
v_a_4800_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4796_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4796_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
case 5:
{
lean_object* v_fn_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v_fn_4808_ = lean_ctor_get(v_x_4759_, 0);
lean_inc_ref(v_fn_4808_);
lean_dec_ref_known(v_x_4759_, 2);
v___x_4809_ = lean_unsigned_to_nat(1u);
v___x_4810_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4808_, v___x_4809_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_);
return v___x_4810_;
}
case 6:
{
uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
lean_dec_ref_known(v_x_4759_, 3);
v___x_4811_ = 0;
v___x_4812_ = lean_box(v___x_4811_);
v___x_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
return v___x_4813_;
}
case 7:
{
uint8_t v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
lean_dec_ref_known(v_x_4759_, 3);
v___x_4814_ = 1;
v___x_4815_ = lean_box(v___x_4814_);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
case 8:
{
lean_object* v_body_4817_; 
v_body_4817_ = lean_ctor_get(v_x_4759_, 3);
lean_inc_ref(v_body_4817_);
lean_dec_ref_known(v_x_4759_, 4);
v_x_4759_ = v_body_4817_;
goto _start;
}
case 9:
{
uint8_t v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
lean_dec_ref_known(v_x_4759_, 1);
v___x_4819_ = 0;
v___x_4820_ = lean_box(v___x_4819_);
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
case 10:
{
lean_object* v_expr_4822_; 
v_expr_4822_ = lean_ctor_get(v_x_4759_, 1);
lean_inc_ref(v_expr_4822_);
lean_dec_ref_known(v_x_4759_, 2);
v_x_4759_ = v_expr_4822_;
goto _start;
}
default: 
{
uint8_t v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
lean_dec_ref(v_x_4759_);
v___x_4824_ = 2;
v___x_4825_ = lean_box(v___x_4824_);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Meta_isTypeQuick(v_x_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v___x_4840_; 
lean_inc_ref(v_e_4834_);
v___x_4840_ = l_Lean_Meta_isTypeQuick(v_e_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4890_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4843_ = v___x_4840_;
v_isShared_4844_ = v_isSharedCheck_4890_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4840_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4890_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
uint8_t v___x_4845_; 
v___x_4845_ = lean_unbox(v_a_4841_);
lean_dec(v_a_4841_);
switch(v___x_4845_)
{
case 0:
{
uint8_t v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
lean_dec_ref(v_e_4834_);
v___x_4846_ = 0;
v___x_4847_ = lean_box(v___x_4846_);
if (v_isShared_4844_ == 0)
{
lean_ctor_set(v___x_4843_, 0, v___x_4847_);
v___x_4849_ = v___x_4843_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
case 1:
{
uint8_t v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4854_; 
lean_dec_ref(v_e_4834_);
v___x_4851_ = 1;
v___x_4852_ = lean_box(v___x_4851_);
if (v_isShared_4844_ == 0)
{
lean_ctor_set(v___x_4843_, 0, v___x_4852_);
v___x_4854_ = v___x_4843_;
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
default: 
{
lean_object* v___x_4856_; 
lean_del_object(v___x_4843_);
lean_inc(v_a_4838_);
lean_inc_ref(v_a_4837_);
lean_inc(v_a_4836_);
lean_inc_ref(v_a_4835_);
v___x_4856_ = lean_infer_type(v_e_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v___x_4858_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc(v_a_4857_);
lean_dec_ref_known(v___x_4856_, 1);
v___x_4858_ = l_Lean_Meta_whnfD(v_a_4857_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4873_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4861_ = v___x_4858_;
v_isShared_4862_ = v_isSharedCheck_4873_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4858_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4873_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
if (lean_obj_tag(v_a_4859_) == 3)
{
uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4866_; 
lean_dec_ref_known(v_a_4859_, 1);
v___x_4863_ = 1;
v___x_4864_ = lean_box(v___x_4863_);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 0, v___x_4864_);
v___x_4866_ = v___x_4861_;
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
else
{
uint8_t v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; 
lean_dec(v_a_4859_);
v___x_4868_ = 0;
v___x_4869_ = lean_box(v___x_4868_);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 0, v___x_4869_);
v___x_4871_ = v___x_4861_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
v_a_4874_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4858_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4858_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
v_a_4882_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4856_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4856_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec_ref(v_e_4834_);
v_a_4891_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4840_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4840_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_){
_start:
{
lean_object* v_res_4905_; 
v_res_4905_ = l_Lean_Meta_isType(v_e_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
lean_dec_ref(v_a_4900_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4906_){
_start:
{
switch(lean_obj_tag(v_x_4906_))
{
case 7:
{
lean_object* v_body_4907_; 
v_body_4907_ = lean_ctor_get(v_x_4906_, 2);
v_x_4906_ = v_body_4907_;
goto _start;
}
case 3:
{
lean_object* v_u_4909_; lean_object* v___x_4910_; 
v_u_4909_ = lean_ctor_get(v_x_4906_, 0);
lean_inc(v_u_4909_);
v___x_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4910_, 0, v_u_4909_);
return v___x_4910_;
}
default: 
{
lean_object* v___x_4911_; 
v___x_4911_ = lean_box(0);
return v___x_4911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4912_);
lean_dec_ref(v_x_4912_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4914_, lean_object* v_body_4915_, lean_object* v_x_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4914_, v_body_4915_, v_x_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
lean_dec(v___y_4920_);
lean_dec_ref(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4925_, lean_object* v_xs_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_l_4933_; 
switch(lean_obj_tag(v_type_4925_))
{
case 3:
{
lean_object* v_u_4936_; 
lean_dec_ref(v_xs_4926_);
v_u_4936_ = lean_ctor_get(v_type_4925_, 0);
lean_inc(v_u_4936_);
lean_dec_ref_known(v_type_4925_, 1);
v_l_4933_ = v_u_4936_;
goto v___jp_4932_;
}
case 7:
{
lean_object* v_binderName_4937_; lean_object* v_binderType_4938_; lean_object* v_body_4939_; uint8_t v_binderInfo_4940_; lean_object* v___f_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v_binderName_4937_ = lean_ctor_get(v_type_4925_, 0);
lean_inc(v_binderName_4937_);
v_binderType_4938_ = lean_ctor_get(v_type_4925_, 1);
lean_inc_ref(v_binderType_4938_);
v_body_4939_ = lean_ctor_get(v_type_4925_, 2);
lean_inc_ref(v_body_4939_);
v_binderInfo_4940_ = lean_ctor_get_uint8(v_type_4925_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4925_, 3);
lean_inc_ref(v_xs_4926_);
v___f_4941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4941_, 0, v_xs_4926_);
lean_closure_set(v___f_4941_, 1, v_body_4939_);
v___x_4942_ = lean_expr_instantiate_rev(v_binderType_4938_, v_xs_4926_);
lean_dec_ref(v_xs_4926_);
lean_dec_ref(v_binderType_4938_);
v___x_4943_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4937_, v_binderInfo_4940_, v___x_4942_, v___f_4941_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
return v___x_4943_;
}
default: 
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4944_ = lean_expr_instantiate_rev(v_type_4925_, v_xs_4926_);
lean_dec_ref(v_xs_4926_);
lean_dec_ref(v_type_4925_);
v___x_4945_ = l_Lean_Meta_whnfD(v___x_4944_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4957_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4948_ = v___x_4945_;
v_isShared_4949_ = v_isSharedCheck_4957_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4945_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4957_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
switch(lean_obj_tag(v_a_4946_))
{
case 3:
{
lean_object* v_u_4950_; 
lean_del_object(v___x_4948_);
v_u_4950_ = lean_ctor_get(v_a_4946_, 0);
lean_inc(v_u_4950_);
lean_dec_ref_known(v_a_4946_, 1);
v_l_4933_ = v_u_4950_;
goto v___jp_4932_;
}
case 7:
{
lean_object* v___x_4951_; 
lean_del_object(v___x_4948_);
v___x_4951_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4925_ = v_a_4946_;
v_xs_4926_ = v___x_4951_;
goto _start;
}
default: 
{
lean_object* v___x_4953_; lean_object* v___x_4955_; 
lean_dec(v_a_4946_);
v___x_4953_ = lean_box(0);
if (v_isShared_4949_ == 0)
{
lean_ctor_set(v___x_4948_, 0, v___x_4953_);
v___x_4955_ = v___x_4948_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4953_);
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
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
v_a_4958_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4945_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4945_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
}
v___jp_4932_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4934_, 0, v_l_4933_);
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
return v___x_4935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4966_, lean_object* v_body_4967_, lean_object* v_x_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_){
_start:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4974_ = lean_array_push(v_xs_4966_, v_x_4968_);
v___x_4975_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4967_, v___x_4974_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4976_, lean_object* v_xs_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4976_, v_xs_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4984_, lean_object* v_cache_4985_, lean_object* v_a_x3f_4986_){
_start:
{
lean_object* v___x_4988_; lean_object* v_mctx_4989_; lean_object* v_zetaDeltaFVarIds_4990_; lean_object* v_postponed_4991_; lean_object* v_diag_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5002_; 
v___x_4988_ = lean_st_ref_take(v_a_4984_);
v_mctx_4989_ = lean_ctor_get(v___x_4988_, 0);
v_zetaDeltaFVarIds_4990_ = lean_ctor_get(v___x_4988_, 2);
v_postponed_4991_ = lean_ctor_get(v___x_4988_, 3);
v_diag_4992_ = lean_ctor_get(v___x_4988_, 4);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5002_ == 0)
{
lean_object* v_unused_5003_; 
v_unused_5003_ = lean_ctor_get(v___x_4988_, 1);
lean_dec(v_unused_5003_);
v___x_4994_ = v___x_4988_;
v_isShared_4995_ = v_isSharedCheck_5002_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_diag_4992_);
lean_inc(v_postponed_4991_);
lean_inc(v_zetaDeltaFVarIds_4990_);
lean_inc(v_mctx_4989_);
lean_dec(v___x_4988_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5002_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4996_; lean_object* v___x_4998_; 
v___x_4996_ = lean_box(0);
if (v_isShared_4995_ == 0)
{
lean_ctor_set(v___x_4994_, 1, v_cache_4985_);
v___x_4998_ = v___x_4994_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_mctx_4989_);
lean_ctor_set(v_reuseFailAlloc_5001_, 1, v_cache_4985_);
lean_ctor_set(v_reuseFailAlloc_5001_, 2, v_zetaDeltaFVarIds_4990_);
lean_ctor_set(v_reuseFailAlloc_5001_, 3, v_postponed_4991_);
lean_ctor_set(v_reuseFailAlloc_5001_, 4, v_diag_4992_);
v___x_4998_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = lean_st_ref_put(v_a_4984_, v___x_4998_);
v___x_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4996_);
return v___x_5000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5004_, lean_object* v_cache_5005_, lean_object* v_a_x3f_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5004_, v_cache_5005_, v_a_x3f_5006_);
lean_dec(v_a_x3f_5006_);
lean_dec(v_a_5004_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5009_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v_cache_5018_; lean_object* v___x_5019_; 
v___x_5016_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5017_ = lean_st_ref_get(v_a_5011_);
v_cache_5018_ = lean_ctor_get(v___x_5017_, 1);
lean_inc_ref(v_cache_5018_);
lean_dec(v___x_5017_);
v___x_5019_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5009_, v___x_5016_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5036_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5022_ = v___x_5019_;
v_isShared_5023_ = v_isSharedCheck_5036_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5019_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5036_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
lean_inc(v_a_5020_);
if (v_isShared_5023_ == 0)
{
lean_ctor_set_tag(v___x_5022_, 1);
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
lean_object* v___x_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
v___x_5026_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5011_, v_cache_5018_, v___x_5025_);
lean_dec_ref(v___x_5025_);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5033_ == 0)
{
lean_object* v_unused_5034_; 
v_unused_5034_ = lean_ctor_get(v___x_5026_, 0);
lean_dec(v_unused_5034_);
v___x_5028_ = v___x_5026_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_dec(v___x_5026_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 0, v_a_5020_);
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5020_);
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
else
{
lean_object* v_a_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
v_a_5037_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5019_, 1);
v___x_5038_ = lean_box(0);
v___x_5039_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5011_, v_cache_5018_, v___x_5038_);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5046_ == 0)
{
lean_object* v_unused_5047_; 
v_unused_5047_ = lean_ctor_get(v___x_5039_, 0);
lean_dec(v_unused_5047_);
v___x_5041_ = v___x_5039_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_dec(v___x_5039_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
lean_ctor_set_tag(v___x_5041_, 1);
lean_ctor_set(v___x_5041_, 0, v_a_5037_);
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5037_);
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
else
{
lean_object* v___x_5048_; 
lean_dec_ref(v_type_5009_);
v___x_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5048_, 0, v___x_5015_);
return v___x_5048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_);
lean_dec(v_a_5053_);
lean_dec_ref(v_a_5052_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v___x_5062_; 
v___x_5062_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5077_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5065_ = v___x_5062_;
v_isShared_5066_ = v_isSharedCheck_5077_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_a_5063_);
lean_dec(v___x_5062_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5077_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
if (lean_obj_tag(v_a_5063_) == 0)
{
uint8_t v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5070_; 
v___x_5067_ = 0;
v___x_5068_ = lean_box(v___x_5067_);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v___x_5068_);
v___x_5070_ = v___x_5065_;
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
else
{
uint8_t v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5075_; 
lean_dec_ref_known(v_a_5063_, 1);
v___x_5072_ = 1;
v___x_5073_ = lean_box(v___x_5072_);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v___x_5073_);
v___x_5075_ = v___x_5065_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
else
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5085_; 
v_a_5078_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5080_ = v___x_5062_;
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5062_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5085_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
if (v_isShared_5081_ == 0)
{
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_){
_start:
{
lean_object* v_res_5092_; 
v_res_5092_ = l_Lean_Meta_isTypeFormerType(v_type_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_);
lean_dec(v_a_5090_);
lean_dec_ref(v_a_5089_);
lean_dec(v_a_5088_);
lean_dec_ref(v_a_5087_);
return v_res_5092_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5093_, lean_object* v_x_5094_){
_start:
{
if (lean_obj_tag(v_x_5093_) == 0)
{
if (lean_obj_tag(v_x_5094_) == 0)
{
uint8_t v___x_5095_; 
v___x_5095_ = 1;
return v___x_5095_;
}
else
{
uint8_t v___x_5096_; 
v___x_5096_ = 0;
return v___x_5096_;
}
}
else
{
if (lean_obj_tag(v_x_5094_) == 0)
{
uint8_t v___x_5097_; 
v___x_5097_ = 0;
return v___x_5097_;
}
else
{
lean_object* v_val_5098_; lean_object* v_val_5099_; uint8_t v___x_5100_; 
v_val_5098_ = lean_ctor_get(v_x_5093_, 0);
v_val_5099_ = lean_ctor_get(v_x_5094_, 0);
v___x_5100_ = lean_level_eq(v_val_5098_, v_val_5099_);
return v___x_5100_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5101_, lean_object* v_x_5102_){
_start:
{
uint8_t v_res_5103_; lean_object* v_r_5104_; 
v_res_5103_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5101_, v_x_5102_);
lean_dec(v_x_5102_);
lean_dec(v_x_5101_);
v_r_5104_ = lean_box(v_res_5103_);
return v_r_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5124_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5124_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5124_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5118_; uint8_t v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5122_; 
v___x_5118_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5119_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5114_, v___x_5118_);
lean_dec(v_a_5114_);
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
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
v_a_5125_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5113_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5113_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Lean_Meta_isPropFormerType(v_type_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_);
lean_dec(v_a_5137_);
lean_dec_ref(v_a_5136_);
lean_dec(v_a_5135_);
lean_dec_ref(v_a_5134_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_){
_start:
{
lean_object* v___x_5146_; 
lean_inc(v_a_5144_);
lean_inc_ref(v_a_5143_);
lean_inc(v_a_5142_);
lean_inc_ref(v_a_5141_);
v___x_5146_ = lean_infer_type(v_e_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5148_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5146_, 1);
v___x_5148_ = l_Lean_Meta_isTypeFormerType(v_a_5147_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_);
return v___x_5148_;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
v_a_5149_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5146_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5146_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Lean_Meta_isTypeFormer(v_e_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_);
lean_dec(v_a_5161_);
lean_dec_ref(v_a_5160_);
lean_dec(v_a_5159_);
lean_dec_ref(v_a_5158_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5164_, lean_object* v_maxFVars_x3f_5165_, lean_object* v_k_5166_, uint8_t v_cleanupAnnotations_5167_, uint8_t v_whnfType_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
lean_object* v___f_5174_; lean_object* v___x_5175_; 
v___f_5174_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5174_, 0, v_k_5166_);
v___x_5175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5164_, v_maxFVars_x3f_5165_, v___f_5174_, v_cleanupAnnotations_5167_, v_whnfType_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_5175_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5175_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v_a_5176_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
}
else
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5191_; 
v_a_5184_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5186_ = v___x_5175_;
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5175_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5191_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5189_; 
if (v_isShared_5187_ == 0)
{
v___x_5189_ = v___x_5186_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5192_, lean_object* v_maxFVars_x3f_5193_, lean_object* v_k_5194_, lean_object* v_cleanupAnnotations_5195_, lean_object* v_whnfType_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5202_; uint8_t v_whnfType_boxed_5203_; lean_object* v_res_5204_; 
v_cleanupAnnotations_boxed_5202_ = lean_unbox(v_cleanupAnnotations_5195_);
v_whnfType_boxed_5203_ = lean_unbox(v_whnfType_5196_);
v_res_5204_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5192_, v_maxFVars_x3f_5193_, v_k_5194_, v_cleanupAnnotations_boxed_5202_, v_whnfType_boxed_5203_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec(v___y_5198_);
lean_dec_ref(v___y_5197_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5205_, lean_object* v_type_5206_, lean_object* v_maxFVars_x3f_5207_, lean_object* v_k_5208_, uint8_t v_cleanupAnnotations_5209_, uint8_t v_whnfType_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5206_, v_maxFVars_x3f_5207_, v_k_5208_, v_cleanupAnnotations_5209_, v_whnfType_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5217_, lean_object* v_type_5218_, lean_object* v_maxFVars_x3f_5219_, lean_object* v_k_5220_, lean_object* v_cleanupAnnotations_5221_, lean_object* v_whnfType_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5228_; uint8_t v_whnfType_boxed_5229_; lean_object* v_res_5230_; 
v_cleanupAnnotations_boxed_5228_ = lean_unbox(v_cleanupAnnotations_5221_);
v_whnfType_boxed_5229_ = lean_unbox(v_whnfType_5222_);
v_res_5230_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5217_, v_type_5218_, v_maxFVars_x3f_5219_, v_k_5220_, v_cleanupAnnotations_boxed_5228_, v_whnfType_boxed_5229_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
return v_res_5230_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5231_, lean_object* v_as_5232_, size_t v_i_5233_, size_t v_stop_5234_){
_start:
{
uint8_t v___x_5235_; 
v___x_5235_ = lean_usize_dec_eq(v_i_5233_, v_stop_5234_);
if (v___x_5235_ == 0)
{
lean_object* v___x_5236_; uint8_t v___x_5237_; 
v___x_5236_ = lean_array_uget_borrowed(v_as_5232_, v_i_5233_);
v___x_5237_ = lean_expr_eqv(v_a_5231_, v___x_5236_);
if (v___x_5237_ == 0)
{
size_t v___x_5238_; size_t v___x_5239_; 
v___x_5238_ = ((size_t)1ULL);
v___x_5239_ = lean_usize_add(v_i_5233_, v___x_5238_);
v_i_5233_ = v___x_5239_;
goto _start;
}
else
{
return v___x_5237_;
}
}
else
{
uint8_t v___x_5241_; 
v___x_5241_ = 0;
return v___x_5241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5242_, lean_object* v_as_5243_, lean_object* v_i_5244_, lean_object* v_stop_5245_){
_start:
{
size_t v_i_boxed_5246_; size_t v_stop_boxed_5247_; uint8_t v_res_5248_; lean_object* v_r_5249_; 
v_i_boxed_5246_ = lean_unbox_usize(v_i_5244_);
lean_dec(v_i_5244_);
v_stop_boxed_5247_ = lean_unbox_usize(v_stop_5245_);
lean_dec(v_stop_5245_);
v_res_5248_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5242_, v_as_5243_, v_i_boxed_5246_, v_stop_boxed_5247_);
lean_dec_ref(v_as_5243_);
lean_dec_ref(v_a_5242_);
v_r_5249_ = lean_box(v_res_5248_);
return v_r_5249_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5250_, lean_object* v_a_5251_){
_start:
{
lean_object* v___x_5252_; lean_object* v___x_5253_; uint8_t v___x_5254_; 
v___x_5252_ = lean_unsigned_to_nat(0u);
v___x_5253_ = lean_array_get_size(v_as_5250_);
v___x_5254_ = lean_nat_dec_lt(v___x_5252_, v___x_5253_);
if (v___x_5254_ == 0)
{
return v___x_5254_;
}
else
{
if (v___x_5254_ == 0)
{
return v___x_5254_;
}
else
{
size_t v___x_5255_; size_t v___x_5256_; uint8_t v___x_5257_; 
v___x_5255_ = ((size_t)0ULL);
v___x_5256_ = lean_usize_of_nat(v___x_5253_);
v___x_5257_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5251_, v_as_5250_, v___x_5255_, v___x_5256_);
return v___x_5257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5258_, lean_object* v_a_5259_){
_start:
{
uint8_t v_res_5260_; lean_object* v_r_5261_; 
v_res_5260_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5258_, v_a_5259_);
lean_dec_ref(v_a_5259_);
lean_dec_ref(v_as_5258_);
v_r_5261_ = lean_box(v_res_5260_);
return v_r_5261_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5262_, lean_object* v_e_5263_){
_start:
{
uint8_t v___x_5264_; lean_object* v_d_5266_; lean_object* v_b_5267_; 
v___x_5264_ = l_Lean_Expr_hasFVar(v_e_5263_);
if (v___x_5264_ == 0)
{
lean_dec_ref(v_e_5263_);
return v___x_5264_;
}
else
{
switch(lean_obj_tag(v_e_5263_))
{
case 7:
{
lean_object* v_binderType_5270_; lean_object* v_body_5271_; 
v_binderType_5270_ = lean_ctor_get(v_e_5263_, 1);
lean_inc_ref(v_binderType_5270_);
v_body_5271_ = lean_ctor_get(v_e_5263_, 2);
lean_inc_ref(v_body_5271_);
lean_dec_ref_known(v_e_5263_, 3);
v_d_5266_ = v_binderType_5270_;
v_b_5267_ = v_body_5271_;
goto v___jp_5265_;
}
case 6:
{
lean_object* v_binderType_5272_; lean_object* v_body_5273_; 
v_binderType_5272_ = lean_ctor_get(v_e_5263_, 1);
lean_inc_ref(v_binderType_5272_);
v_body_5273_ = lean_ctor_get(v_e_5263_, 2);
lean_inc_ref(v_body_5273_);
lean_dec_ref_known(v_e_5263_, 3);
v_d_5266_ = v_binderType_5272_;
v_b_5267_ = v_body_5273_;
goto v___jp_5265_;
}
case 10:
{
lean_object* v_expr_5274_; 
v_expr_5274_ = lean_ctor_get(v_e_5263_, 1);
lean_inc_ref(v_expr_5274_);
lean_dec_ref_known(v_e_5263_, 2);
v_e_5263_ = v_expr_5274_;
goto _start;
}
case 8:
{
lean_object* v_type_5276_; lean_object* v_value_5277_; lean_object* v_body_5278_; uint8_t v___x_5279_; 
v_type_5276_ = lean_ctor_get(v_e_5263_, 1);
lean_inc_ref(v_type_5276_);
v_value_5277_ = lean_ctor_get(v_e_5263_, 2);
lean_inc_ref(v_value_5277_);
v_body_5278_ = lean_ctor_get(v_e_5263_, 3);
lean_inc_ref(v_body_5278_);
lean_dec_ref_known(v_e_5263_, 4);
v___x_5279_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5262_, v_type_5276_);
if (v___x_5279_ == 0)
{
uint8_t v___x_5280_; 
v___x_5280_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5262_, v_value_5277_);
if (v___x_5280_ == 0)
{
v_e_5263_ = v_body_5278_;
goto _start;
}
else
{
lean_dec_ref(v_body_5278_);
return v___x_5264_;
}
}
else
{
lean_dec_ref(v_body_5278_);
lean_dec_ref(v_value_5277_);
return v___x_5264_;
}
}
case 5:
{
lean_object* v_fn_5282_; lean_object* v_arg_5283_; uint8_t v___x_5284_; 
v_fn_5282_ = lean_ctor_get(v_e_5263_, 0);
lean_inc_ref(v_fn_5282_);
v_arg_5283_ = lean_ctor_get(v_e_5263_, 1);
lean_inc_ref(v_arg_5283_);
lean_dec_ref_known(v_e_5263_, 2);
v___x_5284_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5262_, v_fn_5282_);
if (v___x_5284_ == 0)
{
v_e_5263_ = v_arg_5283_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5283_);
return v___x_5264_;
}
}
case 11:
{
lean_object* v_struct_5286_; 
v_struct_5286_ = lean_ctor_get(v_e_5263_, 2);
lean_inc_ref(v_struct_5286_);
lean_dec_ref_known(v_e_5263_, 3);
v_e_5263_ = v_struct_5286_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; 
v_fvarId_5288_ = lean_ctor_get(v_e_5263_, 0);
lean_inc(v_fvarId_5288_);
lean_dec_ref_known(v_e_5263_, 1);
v___x_5289_ = l_Lean_Expr_fvar___override(v_fvarId_5288_);
v___x_5290_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5262_, v___x_5289_);
lean_dec_ref(v___x_5289_);
return v___x_5290_;
}
default: 
{
uint8_t v___x_5291_; 
lean_dec_ref(v_e_5263_);
v___x_5291_ = 0;
return v___x_5291_;
}
}
}
v___jp_5265_:
{
uint8_t v___x_5268_; 
v___x_5268_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5262_, v_d_5266_);
if (v___x_5268_ == 0)
{
v_e_5263_ = v_b_5267_;
goto _start;
}
else
{
lean_dec_ref(v_b_5267_);
return v___x_5264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5292_, lean_object* v_e_5293_){
_start:
{
uint8_t v_res_5294_; lean_object* v_r_5295_; 
v_res_5294_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5292_, v_e_5293_);
lean_dec_ref(v_xs_5292_);
v_r_5295_ = lean_box(v_res_5294_);
return v_r_5295_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5298_ = l_Lean_stringToMessageData(v___x_5297_);
return v___x_5298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5301_ = l_Lean_stringToMessageData(v___x_5300_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5302_, lean_object* v_type_5303_, lean_object* v_as_5304_, size_t v_sz_5305_, size_t v_i_5306_, lean_object* v_b_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v_a_5314_; uint8_t v___x_5318_; 
v___x_5318_ = lean_usize_dec_lt(v_i_5306_, v_sz_5305_);
if (v___x_5318_ == 0)
{
lean_object* v___x_5319_; 
lean_dec_ref(v_type_5303_);
v___x_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5319_, 0, v_b_5307_);
return v___x_5319_;
}
else
{
lean_object* v___x_5320_; lean_object* v_a_5321_; uint8_t v___x_5322_; 
v___x_5320_ = lean_box(0);
v_a_5321_ = lean_array_uget_borrowed(v_as_5304_, v_i_5306_);
lean_inc(v_a_5321_);
v___x_5322_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5302_, v_a_5321_);
if (v___x_5322_ == 0)
{
v_a_5314_ = v___x_5320_;
goto v___jp_5313_;
}
else
{
lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5323_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5321_);
v___x_5324_ = l_Lean_MessageData_ofExpr(v_a_5321_);
v___x_5325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5325_, 0, v___x_5323_);
lean_ctor_set(v___x_5325_, 1, v___x_5324_);
v___x_5326_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5325_);
lean_ctor_set(v___x_5327_, 1, v___x_5326_);
lean_inc_ref(v_type_5303_);
v___x_5328_ = l_Lean_MessageData_ofExpr(v_type_5303_);
v___x_5329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5327_);
lean_ctor_set(v___x_5329_, 1, v___x_5328_);
v___x_5330_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5329_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_dec_ref_known(v___x_5330_, 1);
v_a_5314_ = v___x_5320_;
goto v___jp_5313_;
}
else
{
lean_dec_ref(v_type_5303_);
return v___x_5330_;
}
}
}
v___jp_5313_:
{
size_t v___x_5315_; size_t v___x_5316_; 
v___x_5315_ = ((size_t)1ULL);
v___x_5316_ = lean_usize_add(v_i_5306_, v___x_5315_);
v_i_5306_ = v___x_5316_;
v_b_5307_ = v_a_5314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5331_, lean_object* v_type_5332_, lean_object* v_as_5333_, lean_object* v_sz_5334_, lean_object* v_i_5335_, lean_object* v_b_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
size_t v_sz_boxed_5342_; size_t v_i_boxed_5343_; lean_object* v_res_5344_; 
v_sz_boxed_5342_ = lean_unbox_usize(v_sz_5334_);
lean_dec(v_sz_5334_);
v_i_boxed_5343_ = lean_unbox_usize(v_i_5335_);
lean_dec(v_i_5335_);
v_res_5344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5331_, v_type_5332_, v_as_5333_, v_sz_boxed_5342_, v_i_boxed_5343_, v_b_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v___y_5338_);
lean_dec_ref(v___y_5337_);
lean_dec_ref(v_as_5333_);
lean_dec_ref(v_xs_5331_);
return v_res_5344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5345_, size_t v_i_5346_, lean_object* v_bs_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
uint8_t v___x_5353_; 
v___x_5353_ = lean_usize_dec_lt(v_i_5346_, v_sz_5345_);
if (v___x_5353_ == 0)
{
lean_object* v___x_5354_; 
v___x_5354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5354_, 0, v_bs_5347_);
return v___x_5354_;
}
else
{
lean_object* v_v_5355_; lean_object* v___x_5356_; lean_object* v_bs_x27_5357_; lean_object* v___x_5358_; 
v_v_5355_ = lean_array_uget(v_bs_5347_, v_i_5346_);
v___x_5356_ = lean_unsigned_to_nat(0u);
v_bs_x27_5357_ = lean_array_uset(v_bs_5347_, v_i_5346_, v___x_5356_);
lean_inc(v___y_5351_);
lean_inc_ref(v___y_5350_);
lean_inc(v___y_5349_);
lean_inc_ref(v___y_5348_);
v___x_5358_ = lean_infer_type(v_v_5355_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; size_t v___x_5360_; size_t v___x_5361_; lean_object* v___x_5362_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
lean_dec_ref_known(v___x_5358_, 1);
v___x_5360_ = ((size_t)1ULL);
v___x_5361_ = lean_usize_add(v_i_5346_, v___x_5360_);
v___x_5362_ = lean_array_uset(v_bs_x27_5357_, v_i_5346_, v_a_5359_);
v_i_5346_ = v___x_5361_;
v_bs_5347_ = v___x_5362_;
goto _start;
}
else
{
lean_object* v_a_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5371_; 
lean_dec_ref(v_bs_x27_5357_);
v_a_5364_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5371_ == 0)
{
v___x_5366_ = v___x_5358_;
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_a_5364_);
lean_dec(v___x_5358_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5369_; 
if (v_isShared_5367_ == 0)
{
v___x_5369_ = v___x_5366_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_a_5364_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5372_, lean_object* v_i_5373_, lean_object* v_bs_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
size_t v_sz_boxed_5380_; size_t v_i_boxed_5381_; lean_object* v_res_5382_; 
v_sz_boxed_5380_ = lean_unbox_usize(v_sz_5372_);
lean_dec(v_sz_5372_);
v_i_boxed_5381_ = lean_unbox_usize(v_i_5373_);
lean_dec(v_i_5373_);
v_res_5382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5380_, v_i_boxed_5381_, v_bs_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_);
lean_dec(v___y_5378_);
lean_dec_ref(v___y_5377_);
lean_dec(v___y_5376_);
lean_dec_ref(v___y_5375_);
return v_res_5382_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5384_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5385_ = l_Lean_stringToMessageData(v___x_5384_);
return v___x_5385_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5387_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5388_ = l_Lean_stringToMessageData(v___x_5387_);
return v___x_5388_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5390_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5391_ = l_Lean_stringToMessageData(v___x_5390_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5392_, lean_object* v_n_5393_, lean_object* v_xs_5394_, lean_object* v_x_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
lean_object* v___x_5425_; uint8_t v___x_5426_; 
v___x_5425_ = lean_array_get_size(v_xs_5394_);
v___x_5426_ = lean_nat_dec_eq(v___x_5425_, v_n_5393_);
if (v___x_5426_ == 0)
{
lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
lean_dec_ref(v_xs_5394_);
v___x_5427_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5428_ = l_Lean_MessageData_ofExpr(v_type_5392_);
v___x_5429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5427_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5429_);
lean_ctor_set(v___x_5431_, 1, v___x_5430_);
v___x_5432_ = l_Nat_reprFast(v_n_5393_);
v___x_5433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5432_);
v___x_5434_ = l_Lean_MessageData_ofFormat(v___x_5433_);
v___x_5435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___x_5431_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5435_);
lean_ctor_set(v___x_5437_, 1, v___x_5436_);
v___x_5438_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5437_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_);
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
else
{
lean_dec(v_n_5393_);
goto v___jp_5401_;
}
v___jp_5401_:
{
size_t v_sz_5402_; size_t v___x_5403_; lean_object* v___x_5404_; 
v_sz_5402_ = lean_array_size(v_xs_5394_);
v___x_5403_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5394_);
v___x_5404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5402_, v___x_5403_, v_xs_5394_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_);
if (lean_obj_tag(v___x_5404_) == 0)
{
lean_object* v_a_5405_; lean_object* v___x_5406_; size_t v_sz_5407_; lean_object* v___x_5408_; 
v_a_5405_ = lean_ctor_get(v___x_5404_, 0);
lean_inc(v_a_5405_);
lean_dec_ref_known(v___x_5404_, 1);
v___x_5406_ = lean_box(0);
v_sz_5407_ = lean_array_size(v_a_5405_);
v___x_5408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5394_, v_type_5392_, v_a_5405_, v_sz_5407_, v___x_5403_, v___x_5406_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_);
lean_dec_ref(v_xs_5394_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5415_ == 0)
{
lean_object* v_unused_5416_; 
v_unused_5416_ = lean_ctor_get(v___x_5408_, 0);
lean_dec(v_unused_5416_);
v___x_5410_ = v___x_5408_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_dec(v___x_5408_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 0, v_a_5405_);
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5405_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
else
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5424_; 
lean_dec(v_a_5405_);
v_a_5417_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5419_ = v___x_5408_;
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___x_5408_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5422_; 
if (v_isShared_5420_ == 0)
{
v___x_5422_ = v___x_5419_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5417_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5394_);
lean_dec_ref(v_type_5392_);
return v___x_5404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5447_, lean_object* v_n_5448_, lean_object* v_xs_5449_, lean_object* v_x_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_){
_start:
{
lean_object* v_res_5456_; 
v_res_5456_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5447_, v_n_5448_, v_xs_5449_, v_x_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec_ref(v_x_5450_);
return v_res_5456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5457_, lean_object* v_type_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_){
_start:
{
lean_object* v___f_5464_; lean_object* v___x_5465_; uint8_t v___x_5466_; lean_object* v___x_5467_; 
lean_inc(v_n_5457_);
lean_inc_ref(v_type_5458_);
v___f_5464_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5464_, 0, v_type_5458_);
lean_closure_set(v___f_5464_, 1, v_n_5457_);
v___x_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5465_, 0, v_n_5457_);
v___x_5466_ = 0;
v___x_5467_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5458_, v___x_5465_, v___f_5464_, v___x_5466_, v___x_5466_, v_a_5459_, v_a_5460_, v_a_5461_, v_a_5462_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5468_, lean_object* v_type_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l_Lean_Meta_arrowDomainsN(v_n_5468_, v_type_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_);
lean_dec(v_a_5473_);
lean_dec_ref(v_a_5472_);
lean_dec(v_a_5471_);
lean_dec_ref(v_a_5470_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5476_, lean_object* v_e_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_){
_start:
{
lean_object* v___x_5483_; 
lean_inc(v_a_5481_);
lean_inc_ref(v_a_5480_);
lean_inc(v_a_5479_);
lean_inc_ref(v_a_5478_);
v___x_5483_ = lean_infer_type(v_e_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v_a_5484_; lean_object* v___x_5485_; 
v_a_5484_ = lean_ctor_get(v___x_5483_, 0);
lean_inc(v_a_5484_);
lean_dec_ref_known(v___x_5483_, 1);
v___x_5485_ = l_Lean_Meta_arrowDomainsN(v_n_5476_, v_a_5484_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_);
return v___x_5485_;
}
else
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5493_; 
lean_dec(v_n_5476_);
v_a_5486_ = lean_ctor_get(v___x_5483_, 0);
v_isSharedCheck_5493_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5488_ = v___x_5483_;
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v___x_5483_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5491_; 
if (v_isShared_5489_ == 0)
{
v___x_5491_ = v___x_5488_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5486_);
v___x_5491_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
return v___x_5491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5494_, lean_object* v_e_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_){
_start:
{
lean_object* v_res_5501_; 
v_res_5501_ = l_Lean_Meta_inferArgumentTypesN(v_n_5494_, v_e_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_);
lean_dec(v_a_5499_);
lean_dec_ref(v_a_5498_);
lean_dec(v_a_5497_);
lean_dec_ref(v_a_5496_);
return v_res_5501_;
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
