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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(lean_object* v_a_78_, lean_object* v_x_79_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_78_ = stack[0].m_obj;
lean_object* v_x_79_ = stack[1].m_obj;
uint8_t v_res_92_;
v_res_92_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_78_, v_x_79_);
stack->m_num = v_res_92_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg___boxed(lean_object* v_a_93_, lean_object* v_x_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_93_, v_x_94_);
lean_dec(v_x_94_);
lean_dec_ref(v_a_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(lean_object* v_a_97_, lean_object* v_b_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_dec(v_b_98_);
lean_dec_ref(v_a_97_);
return v_x_99_;
}
else
{
lean_object* v_key_100_; lean_object* v_value_101_; lean_object* v_tail_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_121_; 
v_key_100_ = lean_ctor_get(v_x_99_, 0);
v_value_101_ = lean_ctor_get(v_x_99_, 1);
v_tail_102_ = lean_ctor_get(v_x_99_, 2);
v_isSharedCheck_121_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_121_ == 0)
{
v___x_104_ = v_x_99_;
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_tail_102_);
lean_inc(v_value_101_);
lean_inc(v_key_100_);
lean_dec(v_x_99_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_121_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v___y_107_; lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; uint8_t v___x_119_; 
v_fst_115_ = lean_ctor_get(v_key_100_, 0);
v_snd_116_ = lean_ctor_get(v_key_100_, 1);
v_fst_117_ = lean_ctor_get(v_a_97_, 0);
v_snd_118_ = lean_ctor_get(v_a_97_, 1);
v___x_119_ = l_Lean_ExprStructEq_beq(v_fst_115_, v_fst_117_);
if (v___x_119_ == 0)
{
v___y_107_ = v___x_119_;
goto v___jp_106_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = lean_nat_dec_eq(v_snd_116_, v_snd_118_);
v___y_107_ = v___x_120_;
goto v___jp_106_;
}
v___jp_106_:
{
if (v___y_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_108_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_97_, v_b_98_, v_tail_102_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 2, v___x_108_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_key_100_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_value_101_);
lean_ctor_set(v_reuseFailAlloc_111_, 2, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
else
{
lean_object* v___x_113_; 
lean_dec(v_value_101_);
lean_dec(v_key_100_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_b_98_);
lean_ctor_set(v___x_104_, 0, v_a_97_);
v___x_113_ = v___x_104_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_97_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_b_98_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_tail_102_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(lean_object* v_m_122_, lean_object* v_a_123_, lean_object* v_b_124_){
_start:
{
lean_object* v_size_125_; lean_object* v_buckets_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_173_; 
v_size_125_ = lean_ctor_get(v_m_122_, 0);
v_buckets_126_ = lean_ctor_get(v_m_122_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_m_122_);
if (v_isSharedCheck_173_ == 0)
{
v___x_128_ = v_m_122_;
v_isShared_129_ = v_isSharedCheck_173_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_buckets_126_);
lean_inc(v_size_125_);
lean_dec(v_m_122_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_173_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_fst_130_; lean_object* v_snd_131_; lean_object* v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v_fold_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v_bkt_147_; uint8_t v___x_148_; 
v_fst_130_ = lean_ctor_get(v_a_123_, 0);
v_snd_131_ = lean_ctor_get(v_a_123_, 1);
v___x_132_ = lean_array_get_size(v_buckets_126_);
v___x_133_ = l_Lean_ExprStructEq_hash(v_fst_130_);
v___x_134_ = lean_uint64_of_nat(v_snd_131_);
v___x_135_ = lean_uint64_mix_hash(v___x_133_, v___x_134_);
v___x_136_ = 32ULL;
v___x_137_ = lean_uint64_shift_right(v___x_135_, v___x_136_);
v_fold_138_ = lean_uint64_xor(v___x_135_, v___x_137_);
v___x_139_ = 16ULL;
v___x_140_ = lean_uint64_shift_right(v_fold_138_, v___x_139_);
v___x_141_ = lean_uint64_xor(v_fold_138_, v___x_140_);
v___x_142_ = lean_uint64_to_usize(v___x_141_);
v___x_143_ = lean_usize_of_nat(v___x_132_);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v___x_143_, v___x_144_);
v___x_146_ = lean_usize_land(v___x_142_, v___x_145_);
v_bkt_147_ = lean_array_uget_borrowed(v_buckets_126_, v___x_146_);
v___x_148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_123_, v_bkt_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v_size_x27_150_; lean_object* v___x_151_; lean_object* v_buckets_x27_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_149_ = lean_unsigned_to_nat(1u);
v_size_x27_150_ = lean_nat_add(v_size_125_, v___x_149_);
lean_dec(v_size_125_);
lean_inc(v_bkt_147_);
v___x_151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_151_, 0, v_a_123_);
lean_ctor_set(v___x_151_, 1, v_b_124_);
lean_ctor_set(v___x_151_, 2, v_bkt_147_);
v_buckets_x27_152_ = lean_array_uset(v_buckets_126_, v___x_146_, v___x_151_);
v___x_153_ = lean_unsigned_to_nat(4u);
v___x_154_ = lean_nat_mul(v_size_x27_150_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(3u);
v___x_156_ = lean_nat_div(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_array_get_size(v_buckets_x27_152_);
v___x_158_ = lean_nat_dec_le(v___x_156_, v___x_157_);
lean_dec(v___x_156_);
if (v___x_158_ == 0)
{
lean_object* v_val_159_; lean_object* v___x_161_; 
v_val_159_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_buckets_x27_152_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_val_159_);
lean_ctor_set(v___x_128_, 0, v_size_x27_150_);
v___x_161_ = v___x_128_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_size_x27_150_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_val_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
else
{
lean_object* v___x_164_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_buckets_x27_152_);
lean_ctor_set(v___x_128_, 0, v_size_x27_150_);
v___x_164_ = v___x_128_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_x27_150_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_buckets_x27_152_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v___x_166_; lean_object* v_buckets_x27_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_inc(v_bkt_147_);
v___x_166_ = lean_box(0);
v_buckets_x27_167_ = lean_array_uset(v_buckets_126_, v___x_146_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_123_, v_b_124_, v_bkt_147_);
v___x_169_ = lean_array_uset(v_buckets_x27_167_, v___x_146_, v___x_168_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v___x_169_);
v___x_171_ = v___x_128_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_size_125_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(lean_object* v_msg_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_Lean_instInhabitedExpr;
v___x_176_ = lean_panic_fn_borrowed(v___x_175_, v_msg_174_);
return v___x_176_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___f_179_; 
v___x_178_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_179_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_179_, 0, v___x_178_);
return v___f_179_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(lean_object* v_msg_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___x_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_4808__overap_210_; lean_object* v___x_211_; 
v___x_191_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0));
v___f_192_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1, &l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_once, _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1);
v___f_193_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_193_, 0, v___x_191_);
lean_closure_set(v___f_193_, 1, v___f_192_);
v___x_194_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2));
v___f_195_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3));
v___f_196_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_196_, 0, v___x_194_);
lean_closure_set(v___f_196_, 1, v___f_195_);
v___f_197_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4));
v___f_198_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5));
v___f_199_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6));
v___f_200_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7));
v___f_201_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8));
v___f_202_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9));
v___f_203_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10));
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___f_197_);
lean_ctor_set(v___x_204_, 1, v___f_198_);
v___x_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___f_199_);
lean_ctor_set(v___x_205_, 2, v___f_200_);
lean_ctor_set(v___x_205_, 3, v___f_201_);
lean_ctor_set(v___x_205_, 4, v___f_202_);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___f_203_);
v___x_207_ = l_Lean_MonadStateCacheT_instMonad___redArg(v___f_193_, v___f_196_, v___x_206_);
v___x_208_ = l_Lean_instInhabitedExpr;
v___x_209_ = l_instInhabitedOfMonad___redArg(v___x_207_, v___x_208_);
v___x_4808__overap_210_ = lean_panic_fn_borrowed(v___x_209_, v_msg_189_);
lean_dec(v___x_209_);
v___x_211_ = lean_apply_1(v___x_4808__overap_210_, v___y_190_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(lean_object* v_a_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
else
{
lean_object* v_key_215_; lean_object* v_value_216_; lean_object* v_tail_217_; uint8_t v___y_219_; lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v_fst_224_; lean_object* v_snd_225_; uint8_t v___x_226_; 
v_key_215_ = lean_ctor_get(v_x_213_, 0);
v_value_216_ = lean_ctor_get(v_x_213_, 1);
v_tail_217_ = lean_ctor_get(v_x_213_, 2);
v_fst_222_ = lean_ctor_get(v_key_215_, 0);
v_snd_223_ = lean_ctor_get(v_key_215_, 1);
v_fst_224_ = lean_ctor_get(v_a_212_, 0);
v_snd_225_ = lean_ctor_get(v_a_212_, 1);
v___x_226_ = l_Lean_ExprStructEq_beq(v_fst_222_, v_fst_224_);
if (v___x_226_ == 0)
{
v___y_219_ = v___x_226_;
goto v___jp_218_;
}
else
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_eq(v_snd_223_, v_snd_225_);
v___y_219_ = v___x_227_;
goto v___jp_218_;
}
v___jp_218_:
{
if (v___y_219_ == 0)
{
v_x_213_ = v_tail_217_;
goto _start;
}
else
{
lean_object* v___x_221_; 
lean_inc(v_value_216_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_value_216_);
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg___boxed(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_228_, v_x_229_);
lean_dec(v_x_229_);
lean_dec_ref(v_a_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(lean_object* v_m_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_buckets_233_; lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v_fold_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_buckets_233_ = lean_ctor_get(v_m_231_, 1);
v_fst_234_ = lean_ctor_get(v_a_232_, 0);
v_snd_235_ = lean_ctor_get(v_a_232_, 1);
v___x_236_ = lean_array_get_size(v_buckets_233_);
v___x_237_ = l_Lean_ExprStructEq_hash(v_fst_234_);
v___x_238_ = lean_uint64_of_nat(v_snd_235_);
v___x_239_ = lean_uint64_mix_hash(v___x_237_, v___x_238_);
v___x_240_ = 32ULL;
v___x_241_ = lean_uint64_shift_right(v___x_239_, v___x_240_);
v_fold_242_ = lean_uint64_xor(v___x_239_, v___x_241_);
v___x_243_ = 16ULL;
v___x_244_ = lean_uint64_shift_right(v_fold_242_, v___x_243_);
v___x_245_ = lean_uint64_xor(v_fold_242_, v___x_244_);
v___x_246_ = lean_uint64_to_usize(v___x_245_);
v___x_247_ = lean_usize_of_nat(v___x_236_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_sub(v___x_247_, v___x_248_);
v___x_250_ = lean_usize_land(v___x_246_, v___x_249_);
v___x_251_ = lean_array_uget_borrowed(v_buckets_233_, v___x_250_);
v___x_252_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_232_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg___boxed(lean_object* v_m_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_253_, v_a_254_);
lean_dec_ref(v_a_254_);
lean_dec_ref(v_m_253_);
return v_res_255_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_260_ = lean_unsigned_to_nat(21u);
v___x_261_ = lean_unsigned_to_nat(96u);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_264_ = l_mkPanicMessageWithDecl(v___x_263_, v___x_262_, v___x_261_, v___x_260_, v___x_259_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_266_ = lean_unsigned_to_nat(21u);
v___x_267_ = lean_unsigned_to_nat(97u);
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_270_ = l_mkPanicMessageWithDecl(v___x_269_, v___x_268_, v___x_267_, v___x_266_, v___x_265_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_272_ = lean_unsigned_to_nat(21u);
v___x_273_ = lean_unsigned_to_nat(98u);
v___x_274_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_276_ = l_mkPanicMessageWithDecl(v___x_275_, v___x_274_, v___x_273_, v___x_272_, v___x_271_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_278_ = lean_unsigned_to_nat(21u);
v___x_279_ = lean_unsigned_to_nat(95u);
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_281_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_282_ = l_mkPanicMessageWithDecl(v___x_281_, v___x_280_, v___x_279_, v___x_278_, v___x_277_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(lean_object* v_start_283_, lean_object* v_stop_284_, lean_object* v_args_285_, lean_object* v_e_286_, lean_object* v_offset_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = l_Lean_Expr_looseBVarRange(v_e_286_);
v___x_290_ = lean_nat_dec_le(v___x_289_, v_offset_287_);
lean_dec(v___x_289_);
if (v___x_290_ == 0)
{
if (lean_obj_tag(v_e_286_) == 5)
{
lean_object* v_fn_291_; lean_object* v_arg_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_fn_291_ = lean_ctor_get(v_e_286_, 0);
lean_inc_ref(v_fn_291_);
v_arg_292_ = lean_ctor_get(v_e_286_, 1);
lean_inc_ref(v_arg_292_);
lean_inc(v_offset_287_);
lean_inc_ref(v_e_286_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_e_286_);
lean_ctor_set(v___x_293_, 1, v_offset_287_);
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_288_, v___x_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v___x_295_; lean_object* v_fst_296_; lean_object* v_snd_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
v___x_295_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_283_, v_stop_284_, v_args_285_, v_e_286_, v_fn_291_, v_arg_292_, v_offset_287_, v_a_288_);
v_fst_296_ = lean_ctor_get(v___x_295_, 0);
v_snd_297_ = lean_ctor_get(v___x_295_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v___x_295_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_snd_297_);
lean_inc(v_fst_296_);
lean_dec(v___x_295_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
lean_inc(v_fst_296_);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_297_, v___x_293_, v_fst_296_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_fst_296_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v_val_306_; lean_object* v___x_307_; 
lean_dec_ref_known(v___x_293_, 2);
lean_dec_ref(v_arg_292_);
lean_dec_ref(v_fn_291_);
lean_dec_ref_known(v_e_286_, 2);
lean_dec(v_offset_287_);
v_val_306_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v___x_294_, 1);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_val_306_);
lean_ctor_set(v___x_307_, 1, v_a_288_);
return v___x_307_;
}
}
else
{
lean_object* v___x_308_; 
v___x_308_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_283_, v_stop_284_, v_args_285_, v_e_286_, v_offset_287_, v_a_288_);
return v___x_308_;
}
}
else
{
lean_object* v___x_309_; 
lean_dec(v_offset_287_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_e_286_);
lean_ctor_set(v___x_309_, 1, v_a_288_);
return v___x_309_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2));
v___x_314_ = lean_unsigned_to_nat(18u);
v___x_315_ = lean_unsigned_to_nat(1864u);
v___x_316_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1));
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0));
v___x_318_ = l_mkPanicMessageWithDecl(v___x_317_, v___x_316_, v___x_315_, v___x_314_, v___x_313_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(lean_object* v_start_319_, lean_object* v_stop_320_, lean_object* v_args_321_, lean_object* v_e_322_, lean_object* v_f_323_, lean_object* v_a_324_, lean_object* v_offset_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_330_; 
lean_inc(v_offset_325_);
v___x_327_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_319_, v_stop_320_, v_args_321_, v_f_323_, v_offset_325_, v_a_326_);
v_fst_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_fst_328_);
v_snd_329_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_329_);
lean_dec_ref(v___x_327_);
v___x_330_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_319_, v_stop_320_, v_args_321_, v_a_324_, v_offset_325_, v_snd_329_);
if (lean_obj_tag(v_e_322_) == 5)
{
lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_355_; 
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
v_snd_332_ = lean_ctor_get(v___x_330_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_355_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_355_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_332_);
lean_inc(v_fst_331_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_355_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_fn_336_; lean_object* v_arg_337_; size_t v___x_338_; size_t v___x_339_; uint8_t v___x_340_; 
v_fn_336_ = lean_ctor_get(v_e_322_, 0);
v_arg_337_ = lean_ctor_get(v_e_322_, 1);
v___x_338_ = lean_ptr_addr(v_fn_336_);
v___x_339_ = lean_ptr_addr(v_fst_328_);
v___x_340_ = lean_usize_dec_eq(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v___x_343_; 
lean_dec_ref_known(v_e_322_, 2);
v___x_341_ = l_Lean_Expr_app___override(v_fst_328_, v_fst_331_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_341_);
v___x_343_ = v___x_334_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_snd_332_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
size_t v___x_345_; size_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_ptr_addr(v_arg_337_);
v___x_346_ = lean_ptr_addr(v_fst_331_);
v___x_347_ = lean_usize_dec_eq(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec_ref_known(v_e_322_, 2);
v___x_348_ = l_Lean_Expr_app___override(v_fst_328_, v_fst_331_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_348_);
v___x_350_ = v___x_334_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_snd_332_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
else
{
lean_object* v___x_353_; 
lean_dec(v_fst_331_);
lean_dec(v_fst_328_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v_e_322_);
v___x_353_ = v___x_334_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_e_322_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_snd_332_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
else
{
lean_object* v_snd_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_fst_328_);
lean_dec_ref(v_e_322_);
v_snd_356_ = lean_ctor_get(v___x_330_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_330_, 0);
lean_dec(v_unused_366_);
v___x_358_ = v___x_330_;
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snd_356_);
lean_dec(v___x_330_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_365_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3);
v___x_361_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_360_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_snd_356_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_368_ = lean_unsigned_to_nat(21u);
v___x_369_ = lean_unsigned_to_nat(99u);
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_372_ = l_mkPanicMessageWithDecl(v___x_371_, v___x_370_, v___x_369_, v___x_368_, v___x_367_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object* v_start_373_, lean_object* v_stop_374_, lean_object* v_args_375_, lean_object* v_e_376_, lean_object* v_offset_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = l_Lean_Expr_looseBVarRange(v_e_376_);
v___x_380_ = lean_nat_dec_le(v___x_379_, v_offset_377_);
lean_dec(v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v_fst_383_; lean_object* v_snd_384_; lean_object* v___y_388_; lean_object* v___x_391_; 
lean_inc(v_offset_377_);
lean_inc_ref(v_e_376_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_e_376_);
lean_ctor_set(v___x_381_, 1, v_offset_377_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_378_, v___x_381_);
if (lean_obj_tag(v___x_391_) == 0)
{
switch(lean_obj_tag(v_e_376_))
{
case 0:
{
lean_object* v_deBruijnIndex_392_; lean_object* v___x_393_; 
v_deBruijnIndex_392_ = lean_ctor_get(v_e_376_, 0);
lean_inc(v_deBruijnIndex_392_);
lean_dec_ref_known(v_e_376_, 1);
v___x_393_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(v_start_373_, v_stop_374_, v_args_375_, v_deBruijnIndex_392_, v_offset_377_);
lean_dec(v_offset_377_);
lean_dec(v_deBruijnIndex_392_);
v_fst_383_ = v___x_393_;
v_snd_384_ = v_a_378_;
goto v___jp_382_;
}
case 1:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec_ref_known(v_e_376_, 1);
lean_dec(v_offset_377_);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3);
v___x_395_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_394_, v_a_378_);
v___y_388_ = v___x_395_;
goto v___jp_387_;
}
case 2:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref_known(v_e_376_, 1);
lean_dec(v_offset_377_);
v___x_396_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4);
v___x_397_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_396_, v_a_378_);
v___y_388_ = v___x_397_;
goto v___jp_387_;
}
case 3:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec_ref_known(v_e_376_, 1);
lean_dec(v_offset_377_);
v___x_398_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5);
v___x_399_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_398_, v_a_378_);
v___y_388_ = v___x_399_;
goto v___jp_387_;
}
case 4:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec_ref_known(v_e_376_, 2);
lean_dec(v_offset_377_);
v___x_400_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6);
v___x_401_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_400_, v_a_378_);
v___y_388_ = v___x_401_;
goto v___jp_387_;
}
case 5:
{
lean_object* v_fn_402_; lean_object* v_arg_403_; lean_object* v_head_404_; uint8_t v___x_405_; 
v_fn_402_ = lean_ctor_get(v_e_376_, 0);
v_arg_403_ = lean_ctor_get(v_e_376_, 1);
v_head_404_ = l_Lean_Expr_getAppFn(v_e_376_);
v___x_405_ = l_Lean_Expr_isBVar(v_head_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_inc_ref(v_arg_403_);
lean_inc_ref(v_fn_402_);
lean_dec_ref(v_head_404_);
v___x_406_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_373_, v_stop_374_, v_args_375_, v_e_376_, v_fn_402_, v_arg_403_, v_offset_377_, v_a_378_);
v___y_388_ = v___x_406_;
goto v___jp_387_;
}
else
{
lean_object* v___x_407_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; size_t v_sz_413_; size_t v___x_414_; lean_object* v___x_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_418_; 
lean_inc(v_offset_377_);
v___x_407_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_head_404_, v_offset_377_, v_a_378_);
v_fst_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_fst_408_);
v_snd_409_ = lean_ctor_get(v___x_407_, 1);
lean_inc(v_snd_409_);
lean_dec_ref(v___x_407_);
v___x_410_ = l_Lean_Expr_getAppNumArgs(v_e_376_);
v___x_411_ = lean_mk_empty_array_with_capacity(v___x_410_);
lean_dec(v___x_410_);
v___x_412_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_376_, v___x_411_);
v_sz_413_ = lean_array_size(v___x_412_);
v___x_414_ = ((size_t)0ULL);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_373_, v_stop_374_, v_args_375_, v_offset_377_, v_sz_413_, v___x_414_, v___x_412_, v_snd_409_);
v_fst_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_fst_416_);
v_snd_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_snd_417_);
lean_dec_ref(v___x_415_);
v___x_418_ = l_Lean_Expr_betaRev(v_fst_408_, v_fst_416_, v___x_380_, v___x_380_);
lean_dec(v_fst_416_);
v_fst_383_ = v___x_418_;
v_snd_384_ = v_snd_417_;
goto v___jp_382_;
}
}
case 6:
{
lean_object* v_binderName_419_; lean_object* v_binderType_420_; lean_object* v_body_421_; uint8_t v_binderInfo_422_; lean_object* v___x_423_; lean_object* v_fst_424_; lean_object* v_snd_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; size_t v___x_431_; size_t v___x_432_; uint8_t v___x_433_; 
v_binderName_419_ = lean_ctor_get(v_e_376_, 0);
v_binderType_420_ = lean_ctor_get(v_e_376_, 1);
v_body_421_ = lean_ctor_get(v_e_376_, 2);
v_binderInfo_422_ = lean_ctor_get_uint8(v_e_376_, sizeof(void*)*3 + 8);
lean_inc(v_offset_377_);
lean_inc_ref(v_binderType_420_);
v___x_423_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_binderType_420_, v_offset_377_, v_a_378_);
v_fst_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_fst_424_);
v_snd_425_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_snd_425_);
lean_dec_ref(v___x_423_);
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_offset_377_, v___x_426_);
lean_dec(v_offset_377_);
lean_inc_ref(v_body_421_);
v___x_428_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_body_421_, v___x_427_, v_snd_425_);
v_fst_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_fst_429_);
v_snd_430_ = lean_ctor_get(v___x_428_, 1);
lean_inc(v_snd_430_);
lean_dec_ref(v___x_428_);
v___x_431_ = lean_ptr_addr(v_binderType_420_);
v___x_432_ = lean_ptr_addr(v_fst_424_);
v___x_433_ = lean_usize_dec_eq(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_inc(v_binderName_419_);
lean_dec_ref_known(v_e_376_, 3);
v___x_434_ = l_Lean_Expr_lam___override(v_binderName_419_, v_fst_424_, v_fst_429_, v_binderInfo_422_);
v_fst_383_ = v___x_434_;
v_snd_384_ = v_snd_430_;
goto v___jp_382_;
}
else
{
size_t v___x_435_; size_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = lean_ptr_addr(v_body_421_);
v___x_436_ = lean_ptr_addr(v_fst_429_);
v___x_437_ = lean_usize_dec_eq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_inc(v_binderName_419_);
lean_dec_ref_known(v_e_376_, 3);
v___x_438_ = l_Lean_Expr_lam___override(v_binderName_419_, v_fst_424_, v_fst_429_, v_binderInfo_422_);
v_fst_383_ = v___x_438_;
v_snd_384_ = v_snd_430_;
goto v___jp_382_;
}
else
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_422_, v_binderInfo_422_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_inc(v_binderName_419_);
lean_dec_ref_known(v_e_376_, 3);
v___x_440_ = l_Lean_Expr_lam___override(v_binderName_419_, v_fst_424_, v_fst_429_, v_binderInfo_422_);
v_fst_383_ = v___x_440_;
v_snd_384_ = v_snd_430_;
goto v___jp_382_;
}
else
{
lean_dec(v_fst_429_);
lean_dec(v_fst_424_);
v_fst_383_ = v_e_376_;
v_snd_384_ = v_snd_430_;
goto v___jp_382_;
}
}
}
}
case 7:
{
lean_object* v_binderName_441_; lean_object* v_binderType_442_; lean_object* v_body_443_; uint8_t v_binderInfo_444_; lean_object* v___x_445_; lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_fst_451_; lean_object* v_snd_452_; size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v_binderName_441_ = lean_ctor_get(v_e_376_, 0);
v_binderType_442_ = lean_ctor_get(v_e_376_, 1);
v_body_443_ = lean_ctor_get(v_e_376_, 2);
v_binderInfo_444_ = lean_ctor_get_uint8(v_e_376_, sizeof(void*)*3 + 8);
lean_inc(v_offset_377_);
lean_inc_ref(v_binderType_442_);
v___x_445_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_binderType_442_, v_offset_377_, v_a_378_);
v_fst_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_fst_446_);
v_snd_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_snd_447_);
lean_dec_ref(v___x_445_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_add(v_offset_377_, v___x_448_);
lean_dec(v_offset_377_);
lean_inc_ref(v_body_443_);
v___x_450_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_body_443_, v___x_449_, v_snd_447_);
v_fst_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_fst_451_);
v_snd_452_ = lean_ctor_get(v___x_450_, 1);
lean_inc(v_snd_452_);
lean_dec_ref(v___x_450_);
v___x_453_ = lean_ptr_addr(v_binderType_442_);
v___x_454_ = lean_ptr_addr(v_fst_446_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_inc(v_binderName_441_);
lean_dec_ref_known(v_e_376_, 3);
v___x_456_ = l_Lean_Expr_forallE___override(v_binderName_441_, v_fst_446_, v_fst_451_, v_binderInfo_444_);
v_fst_383_ = v___x_456_;
v_snd_384_ = v_snd_452_;
goto v___jp_382_;
}
else
{
size_t v___x_457_; size_t v___x_458_; uint8_t v___x_459_; 
v___x_457_ = lean_ptr_addr(v_body_443_);
v___x_458_ = lean_ptr_addr(v_fst_451_);
v___x_459_ = lean_usize_dec_eq(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_inc(v_binderName_441_);
lean_dec_ref_known(v_e_376_, 3);
v___x_460_ = l_Lean_Expr_forallE___override(v_binderName_441_, v_fst_446_, v_fst_451_, v_binderInfo_444_);
v_fst_383_ = v___x_460_;
v_snd_384_ = v_snd_452_;
goto v___jp_382_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_444_, v_binderInfo_444_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_inc(v_binderName_441_);
lean_dec_ref_known(v_e_376_, 3);
v___x_462_ = l_Lean_Expr_forallE___override(v_binderName_441_, v_fst_446_, v_fst_451_, v_binderInfo_444_);
v_fst_383_ = v___x_462_;
v_snd_384_ = v_snd_452_;
goto v___jp_382_;
}
else
{
lean_dec(v_fst_451_);
lean_dec(v_fst_446_);
v_fst_383_ = v_e_376_;
v_snd_384_ = v_snd_452_;
goto v___jp_382_;
}
}
}
}
case 8:
{
lean_object* v_declName_463_; lean_object* v_type_464_; lean_object* v_value_465_; lean_object* v_body_466_; uint8_t v_nondep_467_; lean_object* v___x_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v___x_471_; lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; size_t v___x_479_; size_t v___x_480_; uint8_t v___x_481_; 
v_declName_463_ = lean_ctor_get(v_e_376_, 0);
v_type_464_ = lean_ctor_get(v_e_376_, 1);
v_value_465_ = lean_ctor_get(v_e_376_, 2);
v_body_466_ = lean_ctor_get(v_e_376_, 3);
v_nondep_467_ = lean_ctor_get_uint8(v_e_376_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_377_, 2);
lean_inc_ref(v_type_464_);
v___x_468_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_type_464_, v_offset_377_, v_a_378_);
v_fst_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_fst_469_);
v_snd_470_ = lean_ctor_get(v___x_468_, 1);
lean_inc(v_snd_470_);
lean_dec_ref(v___x_468_);
lean_inc_ref(v_value_465_);
v___x_471_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_value_465_, v_offset_377_, v_snd_470_);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_fst_472_);
v_snd_473_ = lean_ctor_get(v___x_471_, 1);
lean_inc(v_snd_473_);
lean_dec_ref(v___x_471_);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_add(v_offset_377_, v___x_474_);
lean_dec(v_offset_377_);
lean_inc_ref(v_body_466_);
v___x_476_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_body_466_, v___x_475_, v_snd_473_);
v_fst_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_fst_477_);
v_snd_478_ = lean_ctor_get(v___x_476_, 1);
lean_inc(v_snd_478_);
lean_dec_ref(v___x_476_);
v___x_479_ = lean_ptr_addr(v_type_464_);
v___x_480_ = lean_ptr_addr(v_fst_469_);
v___x_481_ = lean_usize_dec_eq(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; 
lean_inc(v_declName_463_);
lean_dec_ref_known(v_e_376_, 4);
v___x_482_ = l_Lean_Expr_letE___override(v_declName_463_, v_fst_469_, v_fst_472_, v_fst_477_, v_nondep_467_);
v_fst_383_ = v___x_482_;
v_snd_384_ = v_snd_478_;
goto v___jp_382_;
}
else
{
size_t v___x_483_; size_t v___x_484_; uint8_t v___x_485_; 
v___x_483_ = lean_ptr_addr(v_value_465_);
v___x_484_ = lean_ptr_addr(v_fst_472_);
v___x_485_ = lean_usize_dec_eq(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_inc(v_declName_463_);
lean_dec_ref_known(v_e_376_, 4);
v___x_486_ = l_Lean_Expr_letE___override(v_declName_463_, v_fst_469_, v_fst_472_, v_fst_477_, v_nondep_467_);
v_fst_383_ = v___x_486_;
v_snd_384_ = v_snd_478_;
goto v___jp_382_;
}
else
{
size_t v___x_487_; size_t v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_ptr_addr(v_body_466_);
v___x_488_ = lean_ptr_addr(v_fst_477_);
v___x_489_ = lean_usize_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_inc(v_declName_463_);
lean_dec_ref_known(v_e_376_, 4);
v___x_490_ = l_Lean_Expr_letE___override(v_declName_463_, v_fst_469_, v_fst_472_, v_fst_477_, v_nondep_467_);
v_fst_383_ = v___x_490_;
v_snd_384_ = v_snd_478_;
goto v___jp_382_;
}
else
{
lean_dec(v_fst_477_);
lean_dec(v_fst_472_);
lean_dec(v_fst_469_);
v_fst_383_ = v_e_376_;
v_snd_384_ = v_snd_478_;
goto v___jp_382_;
}
}
}
}
case 9:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref_known(v_e_376_, 1);
lean_dec(v_offset_377_);
v___x_491_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_492_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_491_, v_a_378_);
v___y_388_ = v___x_492_;
goto v___jp_387_;
}
case 10:
{
lean_object* v_data_493_; lean_object* v_expr_494_; lean_object* v___x_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; size_t v___x_498_; size_t v___x_499_; uint8_t v___x_500_; 
v_data_493_ = lean_ctor_get(v_e_376_, 0);
v_expr_494_ = lean_ctor_get(v_e_376_, 1);
lean_inc_ref(v_expr_494_);
v___x_495_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_expr_494_, v_offset_377_, v_a_378_);
v_fst_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v___x_495_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v___x_495_);
v___x_498_ = lean_ptr_addr(v_expr_494_);
v___x_499_ = lean_ptr_addr(v_fst_496_);
v___x_500_ = lean_usize_dec_eq(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_inc(v_data_493_);
lean_dec_ref_known(v_e_376_, 2);
v___x_501_ = l_Lean_Expr_mdata___override(v_data_493_, v_fst_496_);
v_fst_383_ = v___x_501_;
v_snd_384_ = v_snd_497_;
goto v___jp_382_;
}
else
{
lean_dec(v_fst_496_);
v_fst_383_ = v_e_376_;
v_snd_384_ = v_snd_497_;
goto v___jp_382_;
}
}
default: 
{
lean_object* v_typeName_502_; lean_object* v_idx_503_; lean_object* v_struct_504_; lean_object* v___x_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v_typeName_502_ = lean_ctor_get(v_e_376_, 0);
v_idx_503_ = lean_ctor_get(v_e_376_, 1);
v_struct_504_ = lean_ctor_get(v_e_376_, 2);
lean_inc_ref(v_struct_504_);
v___x_505_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_373_, v_stop_374_, v_args_375_, v_struct_504_, v_offset_377_, v_a_378_);
v_fst_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_fst_506_);
v_snd_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_snd_507_);
lean_dec_ref(v___x_505_);
v___x_508_ = lean_ptr_addr(v_struct_504_);
v___x_509_ = lean_ptr_addr(v_fst_506_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_inc(v_idx_503_);
lean_inc(v_typeName_502_);
lean_dec_ref_known(v_e_376_, 3);
v___x_511_ = l_Lean_Expr_proj___override(v_typeName_502_, v_idx_503_, v_fst_506_);
v_fst_383_ = v___x_511_;
v_snd_384_ = v_snd_507_;
goto v___jp_382_;
}
else
{
lean_dec(v_fst_506_);
v_fst_383_ = v_e_376_;
v_snd_384_ = v_snd_507_;
goto v___jp_382_;
}
}
}
}
else
{
lean_object* v_val_512_; lean_object* v___x_513_; 
lean_dec_ref_known(v___x_381_, 2);
lean_dec(v_offset_377_);
lean_dec_ref(v_e_376_);
v_val_512_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_512_);
lean_dec_ref_known(v___x_391_, 1);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_val_512_);
lean_ctor_set(v___x_513_, 1, v_a_378_);
return v___x_513_;
}
v___jp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_inc_ref(v_fst_383_);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_384_, v___x_381_, v_fst_383_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_fst_383_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
return v___x_386_;
}
v___jp_387_:
{
lean_object* v_fst_389_; lean_object* v_snd_390_; 
v_fst_389_ = lean_ctor_get(v___y_388_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v___y_388_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v___y_388_);
v_fst_383_ = v_fst_389_;
v_snd_384_ = v_snd_390_;
goto v___jp_382_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_offset_377_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v_e_376_);
lean_ctor_set(v___x_514_, 1, v_a_378_);
return v___x_514_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_start_515_, lean_object* v_stop_516_, lean_object* v_args_517_, lean_object* v_offset_518_, size_t v_sz_519_, size_t v_i_520_, lean_object* v_bs_521_, lean_object* v___y_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = lean_usize_dec_lt(v_i_520_, v_sz_519_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_dec(v_offset_518_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v_bs_521_);
lean_ctor_set(v___x_524_, 1, v___y_522_);
return v___x_524_;
}
else
{
lean_object* v_v_525_; lean_object* v___x_526_; lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v___x_529_; lean_object* v_bs_x27_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v_v_525_ = lean_array_uget_borrowed(v_bs_521_, v_i_520_);
lean_inc(v_offset_518_);
lean_inc(v_v_525_);
v___x_526_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_515_, v_stop_516_, v_args_517_, v_v_525_, v_offset_518_, v___y_522_);
v_fst_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_fst_527_);
v_snd_528_ = lean_ctor_get(v___x_526_, 1);
lean_inc(v_snd_528_);
lean_dec_ref(v___x_526_);
v___x_529_ = lean_unsigned_to_nat(0u);
v_bs_x27_530_ = lean_array_uset(v_bs_521_, v_i_520_, v___x_529_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_520_, v___x_531_);
v___x_533_ = lean_array_uset(v_bs_x27_530_, v_i_520_, v_fst_527_);
v_i_520_ = v___x_532_;
v_bs_521_ = v___x_533_;
v___y_522_ = v_snd_528_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_start_515_ = stack[0].m_obj;
lean_object* v_stop_516_ = stack[1].m_obj;
lean_object* v_args_517_ = stack[2].m_obj;
lean_object* v_offset_518_ = stack[3].m_obj;
size_t v_sz_519_ = stack[4].m_num;
size_t v_i_520_ = stack[5].m_num;
lean_object* v_bs_521_ = stack[6].m_obj;
lean_object* v___y_522_ = stack[7].m_obj;
lean_object* v_res_535_;
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_515_, v_stop_516_, v_args_517_, v_offset_518_, v_sz_519_, v_i_520_, v_bs_521_, v___y_522_);
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object* v_start_536_, lean_object* v_stop_537_, lean_object* v_args_538_, lean_object* v_offset_539_, lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_bs_542_, lean_object* v___y_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_545_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_536_, v_stop_537_, v_args_538_, v_offset_539_, v_sz_boxed_544_, v_i_boxed_545_, v_bs_542_, v___y_543_);
lean_dec_ref(v_args_538_);
lean_dec(v_stop_537_);
lean_dec(v_start_536_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object* v_start_547_, lean_object* v_stop_548_, lean_object* v_args_549_, lean_object* v_e_550_, lean_object* v_offset_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_547_, v_stop_548_, v_args_549_, v_e_550_, v_offset_551_, v_a_552_);
lean_dec_ref(v_args_549_);
lean_dec(v_stop_548_);
lean_dec(v_start_547_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object* v_start_554_, lean_object* v_stop_555_, lean_object* v_args_556_, lean_object* v_e_557_, lean_object* v_f_558_, lean_object* v_a_559_, lean_object* v_offset_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_554_, v_stop_555_, v_args_556_, v_e_557_, v_f_558_, v_a_559_, v_offset_560_, v_a_561_);
lean_dec_ref(v_args_556_);
lean_dec(v_stop_555_);
lean_dec(v_start_554_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_563_, lean_object* v_stop_564_, lean_object* v_args_565_, lean_object* v_e_566_, lean_object* v_offset_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_563_, v_stop_564_, v_args_565_, v_e_566_, v_offset_567_, v_a_568_);
lean_dec_ref(v_args_565_);
lean_dec(v_stop_564_);
lean_dec(v_start_563_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object* v_00_u03b2_570_, lean_object* v_m_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_571_, v_a_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(v_00_u03b2_574_, v_m_575_, v_a_576_);
lean_dec_ref(v_a_576_);
lean_dec_ref(v_m_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object* v_00_u03b2_578_, lean_object* v_m_579_, lean_object* v_a_580_, lean_object* v_b_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_579_, v_a_580_, v_b_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object* v_00_u03b2_583_, lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_a_584_, v_x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object* v_00_u03b2_587_, lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(v_00_u03b2_587_, v_a_588_, v_x_589_);
lean_dec(v_x_589_);
lean_dec_ref(v_a_588_);
return v_res_590_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object* v_00_u03b2_591_, lean_object* v_a_592_, lean_object* v_x_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_a_592_, v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_592_ = stack[1].m_obj;
lean_object* v_x_593_ = stack[2].m_obj;
uint8_t v_res_595_;
v_res_595_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_box(0), v_a_592_, v_x_593_);
stack->m_num = v_res_595_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object* v_00_u03b2_596_, lean_object* v_a_597_, lean_object* v_x_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(v_00_u03b2_596_, v_a_597_, v_x_598_);
lean_dec(v_x_598_);
lean_dec_ref(v_a_597_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3(lean_object* v_00_u03b2_601_, lean_object* v_data_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3___redArg(v_data_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4(lean_object* v_00_u03b2_604_, lean_object* v_a_605_, lean_object* v_b_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__4___redArg(v_a_605_, v_b_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_609_, lean_object* v_i_610_, lean_object* v_source_611_, lean_object* v_target_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8___redArg(v_i_610_, v_source_611_, v_target_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__3_spec__8_spec__10___redArg(v_x_615_, v_x_616_);
return v___x_617_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_as_618_, size_t v_i_619_, size_t v_stop_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_eq(v_i_619_, v_stop_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_array_uget_borrowed(v_as_618_, v_i_619_);
v___x_623_ = l_Lean_Expr_consumeMData(v___x_622_);
v___x_624_ = l_Lean_Expr_isLambda(v___x_623_);
lean_dec_ref(v___x_623_);
if (v___x_624_ == 0)
{
size_t v___x_625_; size_t v___x_626_; 
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_619_, v___x_625_);
v_i_619_ = v___x_626_;
goto _start;
}
else
{
return v___x_624_;
}
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_618_ = stack[0].m_obj;
size_t v_i_619_ = stack[1].m_num;
size_t v_stop_620_ = stack[2].m_num;
uint8_t v_res_629_;
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_as_618_, v_i_619_, v_stop_620_);
stack->m_num = v_res_629_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object* v_as_630_, lean_object* v_i_631_, lean_object* v_stop_632_){
_start:
{
size_t v_i_boxed_633_; size_t v_stop_boxed_634_; uint8_t v_res_635_; lean_object* v_r_636_; 
v_i_boxed_633_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_stop_boxed_634_ = lean_unbox_usize(v_stop_632_);
lean_dec(v_stop_632_);
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_as_630_, v_i_boxed_633_, v_stop_boxed_634_);
lean_dec_ref(v_as_630_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__0(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_box(0);
v___x_638_ = lean_unsigned_to_nat(16u);
v___x_639_ = lean_mk_array(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__0, &l_Lean_Expr_instantiateBetaRevRange___closed__0_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__0);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_645_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__3));
v___x_646_ = lean_unsigned_to_nat(4u);
v___x_647_ = lean_unsigned_to_nat(39u);
v___x_648_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__2));
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_650_ = l_mkPanicMessageWithDecl(v___x_649_, v___x_648_, v___x_647_, v___x_646_, v___x_645_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_651_, lean_object* v_start_652_, lean_object* v_stop_653_, lean_object* v_args_654_){
_start:
{
lean_object* v___y_656_; uint8_t v___y_668_; uint8_t v___x_675_; 
v___x_675_ = l_Lean_Expr_hasLooseBVars(v_e_651_);
if (v___x_675_ == 0)
{
v___y_668_ = v___x_675_;
goto v___jp_667_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_lt(v_start_652_, v_stop_653_);
v___y_668_ = v___x_676_;
goto v___jp_667_;
}
v___jp_655_:
{
uint8_t v___x_657_; 
v___x_657_ = lean_nat_dec_lt(v_start_652_, v___y_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v___y_656_);
v___x_658_ = lean_expr_instantiate_rev_range(v_e_651_, v_start_652_, v_stop_653_, v_args_654_);
lean_dec(v_stop_653_);
lean_dec_ref(v_e_651_);
return v___x_658_;
}
else
{
size_t v___x_659_; size_t v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_usize_of_nat(v_start_652_);
v___x_660_ = lean_usize_of_nat(v___y_656_);
lean_dec(v___y_656_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_args_654_, v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = lean_expr_instantiate_rev_range(v_e_651_, v_start_652_, v_stop_653_, v_args_654_);
lean_dec(v_stop_653_);
lean_dec_ref(v_e_651_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_fst_666_; 
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__1, &l_Lean_Expr_instantiateBetaRevRange___closed__1_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__1);
v___x_665_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_652_, v_stop_653_, v_args_654_, v_e_651_, v___x_663_, v___x_664_);
lean_dec(v_stop_653_);
v_fst_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_fst_666_);
lean_dec_ref(v___x_665_);
return v_fst_666_;
}
}
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
lean_dec(v_stop_653_);
return v_e_651_;
}
else
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = lean_array_get_size(v_args_654_);
v___x_670_ = lean_nat_dec_le(v_stop_653_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_stop_653_);
lean_dec_ref(v_e_651_);
v___x_671_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__4, &l_Lean_Expr_instantiateBetaRevRange___closed__4_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__4);
v___x_672_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__6(v___x_671_);
return v___x_672_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_lt(v_start_652_, v_stop_653_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = lean_expr_instantiate_rev_range(v_e_651_, v_start_652_, v_stop_653_, v_args_654_);
lean_dec(v_stop_653_);
lean_dec_ref(v_e_651_);
return v___x_674_;
}
else
{
if (v___x_670_ == 0)
{
v___y_656_ = v___x_669_;
goto v___jp_655_;
}
else
{
lean_inc(v_stop_653_);
v___y_656_ = v_stop_653_;
goto v___jp_655_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_677_, lean_object* v_start_678_, lean_object* v_stop_679_, lean_object* v_args_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Expr_instantiateBetaRevRange(v_e_677_, v_start_678_, v_stop_679_, v_args_680_);
lean_dec_ref(v_args_680_);
lean_dec(v_start_678_);
return v_res_681_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_env_689_; uint8_t v___x_690_; lean_object* v_env_691_; lean_object* v___x_692_; lean_object* v_toCold_693_; lean_object* v_mctx_694_; lean_object* v_lctx_695_; lean_object* v_options_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_688_ = lean_st_ref_get(v___y_686_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_env_689_);
lean_dec(v___x_688_);
v___x_690_ = 0;
v_env_691_ = l_Lean_Environment_setRecordingDeps(v_env_689_, v___x_690_);
v___x_692_ = lean_st_ref_get(v___y_684_);
v_toCold_693_ = lean_ctor_get(v___y_685_, 0);
v_mctx_694_ = lean_ctor_get(v___x_692_, 0);
lean_inc_ref(v_mctx_694_);
lean_dec(v___x_692_);
v_lctx_695_ = lean_ctor_get(v___y_683_, 2);
v_options_696_ = lean_ctor_get(v_toCold_693_, 2);
lean_inc_ref(v_options_696_);
lean_inc_ref(v_lctx_695_);
v___x_697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_697_, 0, v_env_691_);
lean_ctor_set(v___x_697_, 1, v_mctx_694_);
lean_ctor_set(v___x_697_, 2, v_lctx_695_);
lean_ctor_set(v___x_697_, 3, v_options_696_);
v___x_698_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_msgData_682_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_682_ = stack[0].m_obj;
lean_object* v___y_683_ = stack[1].m_obj;
lean_object* v___y_684_ = stack[2].m_obj;
lean_object* v___y_685_ = stack[3].m_obj;
lean_object* v___y_686_ = stack[4].m_obj;
lean_object* v_res_700_;
v_res_700_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_ref_714_; lean_object* v___x_715_; lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_ref_714_ = lean_ctor_get(v___y_711_, 2);
v___x_715_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_724_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
lean_inc(v_ref_714_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_ref_714_);
lean_ctor_set(v___x_720_, 1, v_a_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 1);
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_708_ = stack[0].m_obj;
lean_object* v___y_709_ = stack[1].m_obj;
lean_object* v___y_710_ = stack[2].m_obj;
lean_object* v___y_711_ = stack[3].m_obj;
lean_object* v___y_712_ = stack[4].m_obj;
lean_object* v_res_725_;
v_res_725_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
stack->m_obj
 = v_res_725_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_735_ = l_Lean_stringToMessageData(v___x_734_);
return v___x_735_;
}
}
lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_742_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_743_ = l_Lean_indentExpr(v_f_736_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_744_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
return v___x_745_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwFunctionExpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_736_ = stack[0].m_obj;
lean_object* v_a_737_ = stack[1].m_obj;
lean_object* v_a_738_ = stack[2].m_obj;
lean_object* v_a_739_ = stack[3].m_obj;
lean_object* v_a_740_ = stack[4].m_obj;
lean_object* v_res_746_;
v_res_746_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
stack->m_obj
 = v_res_746_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
return v_res_753_;
}
}
lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_754_, lean_object* v_f_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
return v___x_761_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwFunctionExpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_755_ = stack[1].m_obj;
lean_object* v_a_756_ = stack[2].m_obj;
lean_object* v_a_757_ = stack[3].m_obj;
lean_object* v_a_758_ = stack[4].m_obj;
lean_object* v_a_759_ = stack[5].m_obj;
lean_object* v_res_762_;
v_res_762_ = l_Lean_Meta_throwFunctionExpected(lean_box(0), v_f_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_763_, lean_object* v_f_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_763_, v_f_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
return v_res_770_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_771_, lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_778_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_772_ = stack[1].m_obj;
lean_object* v___y_773_ = stack[2].m_obj;
lean_object* v___y_774_ = stack[3].m_obj;
lean_object* v___y_775_ = stack[4].m_obj;
lean_object* v___y_776_ = stack[5].m_obj;
lean_object* v_res_779_;
v_res_779_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_box(0), v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
stack->m_obj
 = v_res_779_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_780_, lean_object* v_msg_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_780_, v_msg_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_788_, lean_object* v_args_789_, lean_object* v_f_790_, lean_object* v_a_791_, lean_object* v_b_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_a_799_; uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_lt(v_a_791_, v_upperBound_788_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_a_791_);
lean_dec_ref(v_f_790_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_b_792_);
return v___x_804_;
}
else
{
lean_object* v_fst_805_; 
v_fst_805_ = lean_ctor_get(v_b_792_, 0);
lean_inc(v_fst_805_);
if (lean_obj_tag(v_fst_805_) == 7)
{
lean_object* v_snd_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_snd_806_ = lean_ctor_get(v_b_792_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_b_792_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_b_792_, 0);
lean_dec(v_unused_815_);
v___x_808_ = v_b_792_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_snd_806_);
lean_dec(v_b_792_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_body_810_; lean_object* v___x_812_; 
v_body_810_ = lean_ctor_get(v_fst_805_, 2);
lean_inc_ref(v_body_810_);
lean_dec_ref_known(v_fst_805_, 3);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v_body_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_body_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_806_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_799_ = v___x_812_;
goto v___jp_798_;
}
}
}
else
{
lean_object* v_snd_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_851_; 
v_snd_816_ = lean_ctor_get(v_b_792_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_b_792_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v_b_792_, 0);
lean_dec(v_unused_852_);
v___x_818_ = v_b_792_;
v_isShared_819_ = v_isSharedCheck_851_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snd_816_);
lean_dec(v_b_792_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_851_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_791_);
lean_inc(v_fst_805_);
v___x_821_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_805_, v_snd_816_, v_a_791_, v_args_789_);
lean_inc(v___y_796_);
lean_inc_ref(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
v___x_822_ = lean_whnf(v___x_821_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
if (lean_obj_tag(v_a_823_) == 7)
{
lean_object* v_body_824_; lean_object* v___x_826_; 
lean_dec(v_snd_816_);
lean_dec(v_fst_805_);
v_body_824_ = lean_ctor_get(v_a_823_, 2);
lean_inc_ref(v_body_824_);
lean_dec_ref_known(v_a_823_, 3);
lean_inc(v_a_791_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_a_791_);
lean_ctor_set(v___x_818_, 0, v_body_824_);
v___x_826_ = v___x_818_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_body_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_a_791_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v_a_799_ = v___x_826_;
goto v___jp_798_;
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec(v_a_823_);
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_nat_add(v_a_791_, v___x_828_);
lean_inc_ref(v_f_790_);
v___x_830_ = l_Lean_mkAppRange(v_f_790_, v___x_820_, v___x_829_, v_args_789_);
lean_dec(v___x_829_);
v___x_831_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_830_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_833_; 
lean_dec_ref_known(v___x_831_, 1);
if (v_isShared_819_ == 0)
{
v___x_833_ = v___x_818_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_fst_805_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_snd_816_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
v_a_799_ = v___x_833_;
goto v___jp_798_;
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
lean_dec(v_fst_805_);
lean_dec(v_a_791_);
lean_dec_ref(v_f_790_);
v_a_835_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_831_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
lean_dec(v_fst_805_);
lean_dec(v_a_791_);
lean_dec_ref(v_f_790_);
v_a_843_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_822_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_822_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
v___jp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_nat_add(v_a_791_, v___x_800_);
lean_dec(v_a_791_);
v_a_791_ = v___x_801_;
v_b_792_ = v_a_799_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_788_ = stack[0].m_obj;
lean_object* v_args_789_ = stack[1].m_obj;
lean_object* v_f_790_ = stack[2].m_obj;
lean_object* v_a_791_ = stack[3].m_obj;
lean_object* v_b_792_ = stack[4].m_obj;
lean_object* v___y_793_ = stack[5].m_obj;
lean_object* v___y_794_ = stack[6].m_obj;
lean_object* v___y_795_ = stack[7].m_obj;
lean_object* v___y_796_ = stack[8].m_obj;
lean_object* v_res_853_;
v_res_853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_788_, v_args_789_, v_f_790_, v_a_791_, v_b_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
stack->m_obj
 = v_res_853_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_854_, lean_object* v_args_855_, lean_object* v_f_856_, lean_object* v_a_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_854_, v_args_855_, v_f_856_, v_a_857_, v_b_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec_ref(v_args_855_);
lean_dec(v_upperBound_854_);
return v_res_864_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_865_, lean_object* v_args_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; 
lean_inc(v_a_870_);
lean_inc_ref(v_a_869_);
lean_inc(v_a_868_);
lean_inc_ref(v_a_867_);
lean_inc_ref(v_f_865_);
v___x_872_ = lean_infer_type(v_f_865_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = lean_array_get_size(v_args_866_);
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_a_873_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_874_, v_args_866_, v_f_865_, v___x_875_, v___x_876_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_888_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_888_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_888_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_888_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_fst_882_; lean_object* v_snd_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v_fst_882_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_fst_882_);
v_snd_883_ = lean_ctor_get(v_a_878_, 1);
lean_inc(v_snd_883_);
lean_dec(v_a_878_);
v___x_884_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_882_, v_snd_883_, v___x_874_, v_args_866_);
lean_dec(v_snd_883_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_877_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_877_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_dec_ref(v_f_865_);
return v___x_872_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_865_ = stack[0].m_obj;
lean_object* v_args_866_ = stack[1].m_obj;
lean_object* v_a_867_ = stack[2].m_obj;
lean_object* v_a_868_ = stack[3].m_obj;
lean_object* v_a_869_ = stack[4].m_obj;
lean_object* v_a_870_ = stack[5].m_obj;
lean_object* v_res_897_;
v_res_897_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_865_, v_args_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_898_, lean_object* v_args_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_898_, v_args_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec_ref(v_args_899_);
return v_res_905_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_906_, lean_object* v_args_907_, lean_object* v_f_908_, lean_object* v_inst_909_, lean_object* v_R_910_, lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v_c_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_906_, v_args_907_, v_f_908_, v_a_911_, v_b_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_919_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_906_ = stack[0].m_obj;
lean_object* v_args_907_ = stack[1].m_obj;
lean_object* v_f_908_ = stack[2].m_obj;
lean_object* v_a_911_ = stack[5].m_obj;
lean_object* v_b_912_ = stack[6].m_obj;
lean_object* v___y_914_ = stack[8].m_obj;
lean_object* v___y_915_ = stack[9].m_obj;
lean_object* v___y_916_ = stack[10].m_obj;
lean_object* v___y_917_ = stack[11].m_obj;
lean_object* v_res_920_;
v_res_920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_906_, v_args_907_, v_f_908_, lean_box(0), lean_box(0), v_a_911_, v_b_912_, lean_box(0), v___y_914_, v___y_915_, v___y_916_, v___y_917_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_921_, lean_object* v_args_922_, lean_object* v_f_923_, lean_object* v_inst_924_, lean_object* v_R_925_, lean_object* v_a_926_, lean_object* v_b_927_, lean_object* v_c_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_921_, v_args_922_, v_f_923_, v_inst_924_, v_R_925_, v_a_926_, v_b_927_, v_c_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec_ref(v_args_922_);
lean_dec(v_upperBound_921_);
return v_res_934_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_938_, lean_object* v_us_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_945_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_946_ = l_Lean_mkConst(v_constName_938_, v_us_939_);
v___x_947_ = l_Lean_MessageData_ofExpr(v___x_946_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_945_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_948_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
return v___x_949_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwIncorrectNumberOfLevels___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_938_ = stack[0].m_obj;
lean_object* v_us_939_ = stack[1].m_obj;
lean_object* v_a_940_ = stack[2].m_obj;
lean_object* v_a_941_ = stack[3].m_obj;
lean_object* v_a_942_ = stack[4].m_obj;
lean_object* v_a_943_ = stack[5].m_obj;
lean_object* v_res_950_;
v_res_950_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_938_, v_us_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
stack->m_obj
 = v_res_950_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_951_, lean_object* v_us_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_951_, v_us_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_958_;
}
}
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_959_, lean_object* v_constName_960_, lean_object* v_us_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_960_, v_us_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_967_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwIncorrectNumberOfLevels_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_960_ = stack[1].m_obj;
lean_object* v_us_961_ = stack[2].m_obj;
lean_object* v_a_962_ = stack[3].m_obj;
lean_object* v_a_963_ = stack[4].m_obj;
lean_object* v_a_964_ = stack[5].m_obj;
lean_object* v_a_965_ = stack[6].m_obj;
lean_object* v_res_968_;
v_res_968_ = l_Lean_Meta_throwIncorrectNumberOfLevels(lean_box(0), v_constName_960_, v_us_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_969_, lean_object* v_constName_970_, lean_object* v_us_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_969_, v_constName_970_, v_us_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
return v_res_977_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_978_, lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_toCold_985_; lean_object* v_currRecDepth_986_; lean_object* v_ref_987_; uint16_t v_optionFlags_988_; uint8_t v_suppressElabErrors_989_; uint8_t v_isRecordingDeps_990_; lean_object* v_ref_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_toCold_985_ = lean_ctor_get(v___y_982_, 0);
v_currRecDepth_986_ = lean_ctor_get(v___y_982_, 1);
v_ref_987_ = lean_ctor_get(v___y_982_, 2);
v_optionFlags_988_ = lean_ctor_get_uint16(v___y_982_, sizeof(void*)*3);
v_suppressElabErrors_989_ = lean_ctor_get_uint8(v___y_982_, sizeof(void*)*3 + 2);
v_isRecordingDeps_990_ = lean_ctor_get_uint8(v___y_982_, sizeof(void*)*3 + 3);
v_ref_991_ = l_Lean_replaceRef(v_ref_978_, v_ref_987_);
lean_inc(v_currRecDepth_986_);
lean_inc_ref(v_toCold_985_);
v___x_992_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_992_, 0, v_toCold_985_);
lean_ctor_set(v___x_992_, 1, v_currRecDepth_986_);
lean_ctor_set(v___x_992_, 2, v_ref_991_);
lean_ctor_set_uint16(v___x_992_, sizeof(void*)*3, v_optionFlags_988_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*3 + 2, v_suppressElabErrors_989_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*3 + 3, v_isRecordingDeps_990_);
v___x_993_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_979_, v___y_980_, v___y_981_, v___x_992_, v___y_983_);
lean_dec_ref_known(v___x_992_, 3);
return v___x_993_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_978_ = stack[0].m_obj;
lean_object* v_msg_979_ = stack[1].m_obj;
lean_object* v___y_980_ = stack[2].m_obj;
lean_object* v___y_981_ = stack[3].m_obj;
lean_object* v___y_982_ = stack[4].m_obj;
lean_object* v___y_983_ = stack[5].m_obj;
lean_object* v_res_994_;
v_res_994_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_978_, v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_995_, lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_995_, v_msg_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v_ref_995_);
return v_res_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
lean_ctor_set(v___x_1009_, 2, v___x_1008_);
lean_ctor_set(v___x_1009_, 3, v___x_1008_);
lean_ctor_set(v___x_1009_, 4, v___x_1007_);
lean_ctor_set(v___x_1009_, 5, v___x_1007_);
lean_ctor_set(v___x_1009_, 6, v___x_1007_);
lean_ctor_set(v___x_1009_, 7, v___x_1007_);
lean_ctor_set(v___x_1009_, 8, v___x_1007_);
lean_ctor_set(v___x_1009_, 9, v___x_1007_);
lean_ctor_set(v___x_1009_, 10, v___x_1007_);
lean_ctor_set(v___x_1009_, 11, v___x_1006_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_unsigned_to_nat(32u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1013_ = ((size_t)5ULL);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_unsigned_to_nat(32u);
v___x_1016_ = lean_mk_empty_array_with_capacity(v___x_1015_);
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1018_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_1016_);
lean_ctor_set(v___x_1018_, 2, v___x_1014_);
lean_ctor_set(v___x_1018_, 3, v___x_1014_);
lean_ctor_set_usize(v___x_1018_, 4, v___x_1013_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1019_ = lean_box(1);
v___x_1020_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_1020_);
lean_ctor_set(v___x_1022_, 2, v___x_1019_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__20));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__22));
v___x_1049_ = l_Lean_stringToMessageData(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__24));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__26));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1056_, lean_object* v_declHint_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_env_1062_; uint8_t v___x_1063_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_st_ref_get(v___y_1058_);
v_env_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_ref(v_env_1062_);
lean_dec(v___x_1061_);
v___x_1063_ = l_Lean_Name_isAnonymous(v_declHint_1057_);
if (v___x_1063_ == 0)
{
uint8_t v_isExporting_1064_; 
v_isExporting_1064_ = lean_ctor_get_uint8(v_env_1062_, sizeof(void*)*13);
if (v_isExporting_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_dec_ref(v_env_1062_);
lean_dec(v_declHint_1057_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_msg_1056_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
lean_inc_ref(v_env_1062_);
v___x_1066_ = l_Lean_Environment_setExporting(v_env_1062_, v___x_1063_);
lean_inc(v_declHint_1057_);
lean_inc_ref(v___x_1066_);
v___x_1067_ = l_Lean_Environment_contains(v___x_1066_, v_declHint_1057_, v_isExporting_1064_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_dec_ref(v___x_1066_);
lean_dec_ref(v_env_1062_);
lean_dec(v_declHint_1057_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_msg_1056_);
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_c_1074_; lean_object* v___x_1075_; 
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1071_ = l_Lean_Options_empty;
v___x_1072_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1066_);
lean_ctor_set(v___x_1072_, 1, v___x_1069_);
lean_ctor_set(v___x_1072_, 2, v___x_1070_);
lean_ctor_set(v___x_1072_, 3, v___x_1071_);
lean_inc(v_declHint_1057_);
v___x_1073_ = l_Lean_MessageData_ofConstName(v_declHint_1057_, v___x_1063_);
v_c_1074_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1074_, 0, v___x_1072_);
lean_ctor_set(v_c_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1062_, v_declHint_1057_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_env_1062_);
lean_dec(v_declHint_1057_);
v___x_1076_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_c_1074_);
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_MessageData_note(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_msg_1056_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1139_; 
v_val_1083_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1085_ = v___x_1075_;
v_isShared_1086_ = v_isSharedCheck_1139_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v___x_1075_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1139_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v_modules_1088_; lean_object* v_moduleNames_1089_; lean_object* v_mod_1090_; uint8_t v___y_1092_; uint8_t v___x_1122_; 
v___x_1087_ = l_Lean_Environment_header(v_env_1062_);
lean_dec_ref(v_env_1062_);
v_modules_1088_ = lean_ctor_get(v___x_1087_, 3);
lean_inc_ref(v_modules_1088_);
v_moduleNames_1089_ = lean_ctor_get(v___x_1087_, 4);
lean_inc_ref(v_moduleNames_1089_);
lean_dec_ref(v___x_1087_);
v_mod_1090_ = lean_array_get(v___x_1060_, v_moduleNames_1089_, v_val_1083_);
lean_dec_ref(v_moduleNames_1089_);
v___x_1122_ = l_Lean_isPrivateName(v_declHint_1057_);
lean_dec(v_declHint_1057_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_array_get_size(v_modules_1088_);
v___x_1124_ = lean_nat_dec_lt(v_val_1083_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v_modules_1088_);
lean_dec(v_val_1083_);
v___y_1092_ = v___x_1122_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1125_; lean_object* v_toImport_1126_; uint8_t v_isExported_1127_; 
v___x_1125_ = lean_array_fget(v_modules_1088_, v_val_1083_);
lean_dec(v_val_1083_);
lean_dec_ref(v_modules_1088_);
v_toImport_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_toImport_1126_);
lean_dec(v___x_1125_);
v_isExported_1127_ = lean_ctor_get_uint8(v_toImport_1126_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1126_);
v___y_1092_ = v_isExported_1127_;
goto v___jp_1091_;
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_modules_1088_);
lean_del_object(v___x_1085_);
lean_dec(v_val_1083_);
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_c_1074_);
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__25);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_MessageData_ofName(v_mod_1090_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__27);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_MessageData_note(v___x_1135_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_msg_1056_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
v___jp_1091_:
{
if (v___y_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_c_1074_);
v___x_1095_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_MessageData_ofName(v_mod_1090_);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_MessageData_note(v___x_1100_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_msg_1056_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1102_);
v___x_1104_ = v___x_1085_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_c_1074_);
v___x_1108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_MessageData_ofName(v_mod_1090_);
lean_inc_ref(v___x_1110_);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__21);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v___x_1110_);
v___x_1115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__23);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_MessageData_note(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_msg_1056_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1118_);
v___x_1120_ = v___x_1085_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
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
lean_object* v___x_1140_; 
lean_dec_ref(v_env_1062_);
lean_dec(v_declHint_1057_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_msg_1056_);
return v___x_1140_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1056_ = stack[0].m_obj;
lean_object* v_declHint_1057_ = stack[1].m_obj;
lean_object* v___y_1058_ = stack[2].m_obj;
lean_object* v_res_1141_;
v_res_1141_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1056_, v_declHint_1057_, v___y_1058_);
stack->m_obj
 = v_res_1141_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1142_, lean_object* v_declHint_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1142_, v_declHint_1143_, v___y_1144_);
lean_dec(v___y_1144_);
return v_res_1146_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1147_, lean_object* v_declHint_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1164_; 
v___x_1154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1147_, v_declHint_1148_, v___y_1152_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1159_ = l_Lean_unknownIdentifierMessageTag;
v___x_1160_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_a_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1147_ = stack[0].m_obj;
lean_object* v_declHint_1148_ = stack[1].m_obj;
lean_object* v___y_1149_ = stack[2].m_obj;
lean_object* v___y_1150_ = stack[3].m_obj;
lean_object* v___y_1151_ = stack[4].m_obj;
lean_object* v___y_1152_ = stack[5].m_obj;
lean_object* v_res_1165_;
v_res_1165_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1147_, v_declHint_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
stack->m_obj
 = v_res_1165_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1166_, lean_object* v_declHint_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1166_, v_declHint_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1174_, lean_object* v_msg_1175_, lean_object* v_declHint_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_a_1183_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1175_, v_declHint_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1174_, v_a_1183_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1184_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1174_ = stack[0].m_obj;
lean_object* v_msg_1175_ = stack[1].m_obj;
lean_object* v_declHint_1176_ = stack[2].m_obj;
lean_object* v___y_1177_ = stack[3].m_obj;
lean_object* v___y_1178_ = stack[4].m_obj;
lean_object* v___y_1179_ = stack[5].m_obj;
lean_object* v___y_1180_ = stack[6].m_obj;
lean_object* v_res_1185_;
v_res_1185_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1174_, v_msg_1175_, v_declHint_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
stack->m_obj
 = v_res_1185_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1186_, lean_object* v_msg_1187_, lean_object* v_declHint_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1186_, v_msg_1187_, v_declHint_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v_ref_1186_);
return v_res_1194_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1200_ = l_Lean_stringToMessageData(v___x_1199_);
return v___x_1200_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1201_, lean_object* v_constName_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1208_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1209_ = 0;
lean_inc(v_constName_1202_);
v___x_1210_ = l_Lean_MessageData_ofConstName(v_constName_1202_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1208_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1201_, v___x_1213_, v_constName_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1214_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1201_ = stack[0].m_obj;
lean_object* v_constName_1202_ = stack[1].m_obj;
lean_object* v___y_1203_ = stack[2].m_obj;
lean_object* v___y_1204_ = stack[3].m_obj;
lean_object* v___y_1205_ = stack[4].m_obj;
lean_object* v___y_1206_ = stack[5].m_obj;
lean_object* v_res_1215_;
v_res_1215_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1201_, v_constName_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
stack->m_obj
 = v_res_1215_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1216_, lean_object* v_constName_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1216_, v_constName_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_ref_1216_);
return v_res_1223_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_ref_1230_; lean_object* v___x_1231_; 
v_ref_1230_ = lean_ctor_get(v___y_1227_, 2);
v___x_1231_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1230_, v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v___x_1231_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1224_ = stack[0].m_obj;
lean_object* v___y_1225_ = stack[1].m_obj;
lean_object* v___y_1226_ = stack[2].m_obj;
lean_object* v___y_1227_ = stack[3].m_obj;
lean_object* v___y_1228_ = stack[4].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1239_;
}
}
lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v_env_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1246_ = lean_st_ref_get(v___y_1244_);
v_env_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc_ref(v_env_1247_);
lean_dec(v___x_1246_);
v___x_1248_ = 0;
lean_inc(v_constName_1240_);
v___x_1249_ = l_Lean_Environment_findConstVal_x3f(v_env_1247_, v_constName_1240_, v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1250_;
}
else
{
lean_object* v_val_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_constName_1240_);
v_val_1251_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1249_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_val_1251_);
lean_dec(v___x_1249_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set_tag(v___x_1253_, 0);
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_val_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1240_ = stack[0].m_obj;
lean_object* v___y_1241_ = stack[1].m_obj;
lean_object* v___y_1242_ = stack[2].m_obj;
lean_object* v___y_1243_ = stack[3].m_obj;
lean_object* v___y_1244_ = stack[4].m_obj;
lean_object* v_res_1259_;
v_res_1259_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
stack->m_obj
 = v_res_1259_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1266_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1267_, lean_object* v_us_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
lean_inc(v_c_1267_);
v___x_1274_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v_levelParams_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v_levelParams_1276_ = lean_ctor_get(v_a_1275_, 1);
v___x_1277_ = l_List_lengthTR___redArg(v_levelParams_1276_);
v___x_1278_ = l_List_lengthTR___redArg(v_us_1268_);
v___x_1279_ = lean_nat_dec_eq(v___x_1277_, v___x_1278_);
lean_dec(v___x_1278_);
lean_dec(v___x_1277_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v_a_1275_);
v___x_1280_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1267_, v_us_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; 
lean_dec(v_c_1267_);
v___x_1281_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1275_, v_us_1268_, v_a_1272_);
return v___x_1281_;
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_us_1268_);
lean_dec(v_c_1267_);
v_a_1282_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1274_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1274_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1267_ = stack[0].m_obj;
lean_object* v_us_1268_ = stack[1].m_obj;
lean_object* v_a_1269_ = stack[2].m_obj;
lean_object* v_a_1270_ = stack[3].m_obj;
lean_object* v_a_1271_ = stack[4].m_obj;
lean_object* v_a_1272_ = stack[5].m_obj;
lean_object* v_res_1290_;
v_res_1290_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1267_, v_us_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
stack->m_obj
 = v_res_1290_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1291_, lean_object* v_us_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1291_, v_us_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1298_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1299_, lean_object* v_constName_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1300_ = stack[1].m_obj;
lean_object* v___y_1301_ = stack[2].m_obj;
lean_object* v___y_1302_ = stack[3].m_obj;
lean_object* v___y_1303_ = stack[4].m_obj;
lean_object* v___y_1304_ = stack[5].m_obj;
lean_object* v_res_1307_;
v_res_1307_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_box(0), v_constName_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
stack->m_obj
 = v_res_1307_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_constName_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1308_, v_constName_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1315_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1316_, lean_object* v_ref_1317_, lean_object* v_constName_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1317_, v_constName_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1317_ = stack[1].m_obj;
lean_object* v_constName_1318_ = stack[2].m_obj;
lean_object* v___y_1319_ = stack[3].m_obj;
lean_object* v___y_1320_ = stack[4].m_obj;
lean_object* v___y_1321_ = stack[5].m_obj;
lean_object* v___y_1322_ = stack[6].m_obj;
lean_object* v_res_1325_;
v_res_1325_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_box(0), v_ref_1317_, v_constName_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
stack->m_obj
 = v_res_1325_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_ref_1327_, lean_object* v_constName_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1326_, v_ref_1327_, v_constName_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v_ref_1327_);
return v_res_1334_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1335_, lean_object* v_ref_1336_, lean_object* v_msg_1337_, lean_object* v_declHint_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1336_, v_msg_1337_, v_declHint_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1336_ = stack[1].m_obj;
lean_object* v_msg_1337_ = stack[2].m_obj;
lean_object* v_declHint_1338_ = stack[3].m_obj;
lean_object* v___y_1339_ = stack[4].m_obj;
lean_object* v___y_1340_ = stack[5].m_obj;
lean_object* v___y_1341_ = stack[6].m_obj;
lean_object* v___y_1342_ = stack[7].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_box(0), v_ref_1336_, v_msg_1337_, v_declHint_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1346_, lean_object* v_ref_1347_, lean_object* v_msg_1348_, lean_object* v_declHint_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1346_, v_ref_1347_, v_msg_1348_, v_declHint_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v_ref_1347_);
return v_res_1355_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1356_, lean_object* v_declHint_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1356_, v_declHint_1357_, v___y_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1356_ = stack[0].m_obj;
lean_object* v_declHint_1357_ = stack[1].m_obj;
lean_object* v___y_1358_ = stack[2].m_obj;
lean_object* v___y_1359_ = stack[3].m_obj;
lean_object* v___y_1360_ = stack[4].m_obj;
lean_object* v___y_1361_ = stack[5].m_obj;
lean_object* v_res_1364_;
v_res_1364_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1356_, v_declHint_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
stack->m_obj
 = v_res_1364_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1365_, lean_object* v_declHint_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1365_, v_declHint_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1372_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1373_, lean_object* v_ref_1374_, lean_object* v_msg_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1374_, v_msg_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1374_ = stack[1].m_obj;
lean_object* v_msg_1375_ = stack[2].m_obj;
lean_object* v___y_1376_ = stack[3].m_obj;
lean_object* v___y_1377_ = stack[4].m_obj;
lean_object* v___y_1378_ = stack[5].m_obj;
lean_object* v___y_1379_ = stack[6].m_obj;
lean_object* v_res_1382_;
v_res_1382_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_box(0), v_ref_1374_, v_msg_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_ref_1384_, lean_object* v_msg_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1383_, v_ref_1384_, v_msg_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v_ref_1384_);
return v_res_1391_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1394_ = l_Lean_stringToMessageData(v___x_1393_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1398_, lean_object* v_idx_1399_, lean_object* v_e_1400_, lean_object* v_a_1401_, lean_object* v_00_u03b1_1402_, lean_object* v_x_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1410_ = l_Lean_mkProj(v_structName_1398_, v_idx_1399_, v_e_1400_);
v___x_1411_ = l_Lean_indentExpr(v___x_1410_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1409_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = l_Lean_indentExpr(v_a_1401_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1416_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1417_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_1398_ = stack[0].m_obj;
lean_object* v_idx_1399_ = stack[1].m_obj;
lean_object* v_e_1400_ = stack[2].m_obj;
lean_object* v_a_1401_ = stack[3].m_obj;
lean_object* v_x_1403_ = stack[5].m_obj;
lean_object* v___y_1404_ = stack[6].m_obj;
lean_object* v___y_1405_ = stack[7].m_obj;
lean_object* v___y_1406_ = stack[8].m_obj;
lean_object* v___y_1407_ = stack[9].m_obj;
lean_object* v_res_1418_;
v_res_1418_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1398_, v_idx_1399_, v_e_1400_, v_a_1401_, lean_box(0), v_x_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
stack->m_obj
 = v_res_1418_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1419_, lean_object* v_idx_1420_, lean_object* v_e_1421_, lean_object* v_a_1422_, lean_object* v_00_u03b1_1423_, lean_object* v_x_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1419_, v_idx_1420_, v_e_1421_, v_a_1422_, v_00_u03b1_1423_, v_x_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
return v_res_1430_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_env_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1437_ = lean_st_ref_get(v___y_1435_);
v_env_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_env_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = 0;
lean_inc(v_constName_1431_);
v___x_1440_ = l_Lean_Environment_find_x3f(v_env_1438_, v_constName_1431_, v___x_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1441_;
}
else
{
lean_object* v_val_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_constName_1431_);
v_val_1442_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1440_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_val_1442_);
lean_dec(v___x_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 0);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_val_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1431_ = stack[0].m_obj;
lean_object* v___y_1432_ = stack[1].m_obj;
lean_object* v___y_1433_ = stack[2].m_obj;
lean_object* v___y_1434_ = stack[3].m_obj;
lean_object* v___y_1435_ = stack[4].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
return v_res_1457_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1458_, lean_object* v_structName_1459_, lean_object* v_e_1460_, lean_object* v_idx_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_b_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_a_1471_; uint8_t v___x_1475_; 
v___x_1475_ = lean_nat_dec_lt(v_a_1463_, v_upperBound_1458_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_idx_1461_);
lean_dec_ref(v_e_1460_);
lean_dec(v_structName_1459_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_b_1464_);
return v___x_1476_;
}
else
{
lean_object* v___x_1477_; 
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
v___x_1477_ = lean_whnf(v_b_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
if (lean_obj_tag(v_a_1478_) == 7)
{
lean_object* v_body_1479_; uint8_t v___x_1480_; 
v_body_1479_ = lean_ctor_get(v_a_1478_, 2);
lean_inc_ref(v_body_1479_);
lean_dec_ref_known(v_a_1478_, 3);
v___x_1480_ = l_Lean_Expr_hasLooseBVars(v_body_1479_);
if (v___x_1480_ == 0)
{
v_a_1471_ = v_body_1479_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_inc_ref(v_e_1460_);
lean_inc(v_a_1463_);
lean_inc(v_structName_1459_);
v___x_1481_ = l_Lean_mkProj(v_structName_1459_, v_a_1463_, v_e_1460_);
v___x_1482_ = lean_expr_instantiate1(v_body_1479_, v___x_1481_);
lean_dec_ref(v___x_1481_);
lean_dec_ref(v_body_1479_);
v_a_1471_ = v___x_1482_;
goto v___jp_1470_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1483_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1460_);
lean_inc(v_idx_1461_);
lean_inc(v_structName_1459_);
v___x_1484_ = l_Lean_mkProj(v_structName_1459_, v_idx_1461_, v_e_1460_);
v___x_1485_ = l_Lean_indentExpr(v___x_1484_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1483_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
lean_inc_ref(v_a_1462_);
v___x_1489_ = l_Lean_indentExpr(v_a_1462_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1490_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
v_a_1471_ = v_a_1478_;
goto v___jp_1470_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_a_1478_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_idx_1461_);
lean_dec_ref(v_e_1460_);
lean_dec(v_structName_1459_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
else
{
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_idx_1461_);
lean_dec_ref(v_e_1460_);
lean_dec(v_structName_1459_);
return v___x_1477_;
}
}
v___jp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_add(v_a_1463_, v___x_1472_);
lean_dec(v_a_1463_);
v_a_1463_ = v___x_1473_;
v_b_1464_ = v_a_1471_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1458_ = stack[0].m_obj;
lean_object* v_structName_1459_ = stack[1].m_obj;
lean_object* v_e_1460_ = stack[2].m_obj;
lean_object* v_idx_1461_ = stack[3].m_obj;
lean_object* v_a_1462_ = stack[4].m_obj;
lean_object* v_a_1463_ = stack[5].m_obj;
lean_object* v_b_1464_ = stack[6].m_obj;
lean_object* v___y_1465_ = stack[7].m_obj;
lean_object* v___y_1466_ = stack[8].m_obj;
lean_object* v___y_1467_ = stack[9].m_obj;
lean_object* v___y_1468_ = stack[10].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1458_, v_structName_1459_, v_e_1460_, v_idx_1461_, v_a_1462_, v_a_1463_, v_b_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1501_, lean_object* v_structName_1502_, lean_object* v_e_1503_, lean_object* v_idx_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1501_, v_structName_1502_, v_e_1503_, v_idx_1504_, v_a_1505_, v_a_1506_, v_b_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v_upperBound_1501_);
return v_res_1513_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1514_, lean_object* v_structName_1515_, lean_object* v_e_1516_, lean_object* v_idx_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_a_1527_; uint8_t v___x_1531_; 
v___x_1531_ = lean_nat_dec_lt(v_a_1519_, v_upperBound_1514_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_idx_1517_);
lean_dec_ref(v_e_1516_);
lean_dec(v_structName_1515_);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_b_1520_);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; 
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1523_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
v___x_1533_ = lean_whnf(v_b_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
if (lean_obj_tag(v_a_1534_) == 7)
{
lean_object* v_body_1535_; uint8_t v___x_1536_; 
v_body_1535_ = lean_ctor_get(v_a_1534_, 2);
lean_inc_ref(v_body_1535_);
lean_dec_ref_known(v_a_1534_, 3);
v___x_1536_ = l_Lean_Expr_hasLooseBVars(v_body_1535_);
if (v___x_1536_ == 0)
{
v_a_1527_ = v_body_1535_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_inc_ref(v_e_1516_);
lean_inc(v_a_1519_);
lean_inc(v_structName_1515_);
v___x_1537_ = l_Lean_mkProj(v_structName_1515_, v_a_1519_, v_e_1516_);
v___x_1538_ = lean_expr_instantiate1(v_body_1535_, v___x_1537_);
lean_dec_ref(v___x_1537_);
lean_dec_ref(v_body_1535_);
v_a_1527_ = v___x_1538_;
goto v___jp_1526_;
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1539_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1516_);
lean_inc(v_idx_1517_);
lean_inc(v_structName_1515_);
v___x_1540_ = l_Lean_mkProj(v_structName_1515_, v_idx_1517_, v_e_1516_);
v___x_1541_ = l_Lean_indentExpr(v___x_1540_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1539_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
lean_inc_ref(v_a_1518_);
v___x_1545_ = l_Lean_indentExpr(v_a_1518_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1546_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_dec_ref_known(v___x_1547_, 1);
v_a_1527_ = v_a_1534_;
goto v___jp_1526_;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1534_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_idx_1517_);
lean_dec_ref(v_e_1516_);
lean_dec(v_structName_1515_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
else
{
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_idx_1517_);
lean_dec_ref(v_e_1516_);
lean_dec(v_structName_1515_);
return v___x_1533_;
}
}
v___jp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_nat_add(v_a_1519_, v___x_1528_);
lean_dec(v_a_1519_);
v___x_1530_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1514_, v_structName_1515_, v_e_1516_, v_idx_1517_, v_a_1518_, v___x_1529_, v_a_1527_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1530_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1514_ = stack[0].m_obj;
lean_object* v_structName_1515_ = stack[1].m_obj;
lean_object* v_e_1516_ = stack[2].m_obj;
lean_object* v_idx_1517_ = stack[3].m_obj;
lean_object* v_a_1518_ = stack[4].m_obj;
lean_object* v_a_1519_ = stack[5].m_obj;
lean_object* v_b_1520_ = stack[6].m_obj;
lean_object* v___y_1521_ = stack[7].m_obj;
lean_object* v___y_1522_ = stack[8].m_obj;
lean_object* v___y_1523_ = stack[9].m_obj;
lean_object* v___y_1524_ = stack[10].m_obj;
lean_object* v_res_1556_;
v_res_1556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1514_, v_structName_1515_, v_e_1516_, v_idx_1517_, v_a_1518_, v_a_1519_, v_b_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
stack->m_obj
 = v_res_1556_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1557_, lean_object* v_structName_1558_, lean_object* v_e_1559_, lean_object* v_idx_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1557_, v_structName_1558_, v_e_1559_, v_idx_1560_, v_a_1561_, v_a_1562_, v_b_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v_upperBound_1557_);
return v_res_1569_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1570_; lean_object* v_dummy_1571_; 
v___x_1570_ = lean_box(0);
v_dummy_1571_ = l_Lean_Expr_sort___override(v___x_1570_);
return v_dummy_1571_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1572_, lean_object* v_idx_1573_, lean_object* v_e_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v___x_1580_; 
lean_inc(v_a_1578_);
lean_inc_ref(v_a_1577_);
lean_inc(v_a_1576_);
lean_inc_ref(v_a_1575_);
lean_inc_ref(v_e_1574_);
v___x_1580_ = lean_infer_type(v_e_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
lean_inc(v_a_1578_);
lean_inc_ref(v_a_1577_);
lean_inc(v_a_1576_);
lean_inc_ref(v_a_1575_);
v___x_1582_ = lean_whnf(v_a_1581_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l_Lean_Expr_getAppFn(v_a_1583_);
if (lean_obj_tag(v___x_1584_) == 4)
{
lean_object* v_declName_1585_; lean_object* v_us_1586_; lean_object* v___x_1587_; lean_object* v_env_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; 
v_declName_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_declName_1585_);
v_us_1586_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_us_1586_);
lean_dec_ref_known(v___x_1584_, 2);
v___x_1587_ = lean_st_ref_get(v_a_1578_);
v_env_1591_ = lean_ctor_get(v___x_1587_, 0);
lean_inc_ref(v_env_1591_);
lean_dec(v___x_1587_);
v___x_1592_ = 0;
v___x_1593_ = l_Lean_Environment_find_x3f(v_env_1591_, v_declName_1585_, v___x_1592_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v_us_1586_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1594_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1595_;
}
else
{
lean_object* v_val_1596_; 
v_val_1596_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___x_1593_, 1);
if (lean_obj_tag(v_val_1596_) == 5)
{
lean_object* v_val_1597_; lean_object* v_ctors_1598_; 
v_val_1597_ = lean_ctor_get(v_val_1596_, 0);
lean_inc_ref(v_val_1597_);
lean_dec_ref_known(v_val_1596_, 1);
v_ctors_1598_ = lean_ctor_get(v_val_1597_, 4);
lean_inc(v_ctors_1598_);
if (lean_obj_tag(v_ctors_1598_) == 1)
{
lean_object* v_tail_1599_; 
v_tail_1599_ = lean_ctor_get(v_ctors_1598_, 1);
if (lean_obj_tag(v_tail_1599_) == 0)
{
lean_object* v_toConstantVal_1600_; lean_object* v_numParams_1601_; lean_object* v_numIndices_1602_; lean_object* v_head_1603_; lean_object* v___x_1604_; 
v_toConstantVal_1600_ = lean_ctor_get(v_val_1597_, 0);
lean_inc_ref(v_toConstantVal_1600_);
v_numParams_1601_ = lean_ctor_get(v_val_1597_, 1);
lean_inc(v_numParams_1601_);
v_numIndices_1602_ = lean_ctor_get(v_val_1597_, 2);
lean_inc(v_numIndices_1602_);
lean_dec_ref(v_val_1597_);
v_head_1603_ = lean_ctor_get(v_ctors_1598_, 0);
lean_inc(v_head_1603_);
lean_dec_ref_known(v_ctors_1598_, 2);
v___x_1604_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1603_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
if (lean_obj_tag(v_a_1605_) == 6)
{
lean_object* v_val_1606_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v_name_1646_; uint8_t v___x_1647_; 
v_val_1606_ = lean_ctor_get(v_a_1605_, 0);
lean_inc_ref(v_val_1606_);
lean_dec_ref_known(v_a_1605_, 1);
v_name_1646_ = lean_ctor_get(v_toConstantVal_1600_, 0);
lean_inc(v_name_1646_);
lean_dec_ref(v_toConstantVal_1600_);
v___x_1647_ = lean_name_eq(v_name_1646_, v_structName_1572_);
lean_dec(v_name_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v_val_1606_);
lean_dec(v_numIndices_1602_);
lean_dec(v_numParams_1601_);
lean_dec(v_us_1586_);
v___x_1648_ = lean_box(0);
v___x_1649_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1648_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
else
{
v___y_1608_ = v_a_1575_;
v___y_1609_ = v_a_1576_;
v___y_1610_ = v_a_1577_;
v___y_1611_ = v_a_1578_;
goto v___jp_1607_;
}
v___jp_1607_:
{
lean_object* v_dummy_1612_; lean_object* v_nargs_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_dummy_1612_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1613_ = l_Lean_Expr_getAppNumArgs(v_a_1583_);
lean_inc(v_nargs_1613_);
v___x_1614_ = lean_mk_array(v_nargs_1613_, v_dummy_1612_);
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_sub(v_nargs_1613_, v___x_1615_);
lean_dec(v_nargs_1613_);
lean_inc(v_a_1583_);
v___x_1617_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1583_, v___x_1614_, v___x_1616_);
v___x_1618_ = lean_nat_add(v_numParams_1601_, v_numIndices_1602_);
lean_dec(v_numIndices_1602_);
v___x_1619_ = lean_array_get_size(v___x_1617_);
v___x_1620_ = lean_nat_dec_eq(v___x_1618_, v___x_1619_);
lean_dec(v___x_1618_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v___x_1617_);
lean_dec_ref(v_val_1606_);
lean_dec(v_numParams_1601_);
lean_dec(v_us_1586_);
v___x_1621_ = lean_box(0);
v___x_1622_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1621_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1622_;
}
else
{
lean_object* v_toConstantVal_1623_; lean_object* v_name_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_toConstantVal_1623_ = lean_ctor_get(v_val_1606_, 0);
lean_inc_ref(v_toConstantVal_1623_);
lean_dec_ref(v_val_1606_);
v_name_1624_ = lean_ctor_get(v_toConstantVal_1623_, 0);
lean_inc(v_name_1624_);
lean_dec_ref(v_toConstantVal_1623_);
v___x_1625_ = l_Lean_mkConst(v_name_1624_, v_us_1586_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = l_Array_toSubarray___redArg(v___x_1617_, v___x_1626_, v_numParams_1601_);
v___x_1628_ = l_Subarray_copy___redArg(v___x_1627_);
v___x_1629_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1625_, v___x_1628_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec_ref(v___x_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
lean_inc(v_a_1583_);
lean_inc_ref(v_e_1574_);
lean_inc(v_structName_1572_);
lean_inc(v_idx_1573_);
v___x_1631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1573_, v_structName_1572_, v_e_1574_, v_idx_1573_, v_a_1583_, v___x_1626_, v_a_1630_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1610_);
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1608_);
v___x_1633_ = lean_whnf(v_a_1632_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1645_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
if (lean_obj_tag(v_a_1634_) == 7)
{
lean_object* v_binderType_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec(v_a_1583_);
lean_dec_ref(v_e_1574_);
lean_dec(v_idx_1573_);
lean_dec(v_structName_1572_);
v_binderType_1638_ = lean_ctor_get(v_a_1634_, 1);
lean_inc_ref(v_binderType_1638_);
lean_dec_ref_known(v_a_1634_, 3);
v___x_1639_ = lean_expr_consume_type_annotations(v_binderType_1638_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_del_object(v___x_1636_);
lean_dec(v_a_1634_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1643_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1644_;
}
}
}
else
{
lean_dec(v_a_1583_);
lean_dec_ref(v_e_1574_);
lean_dec(v_idx_1573_);
lean_dec(v_structName_1572_);
return v___x_1633_;
}
}
else
{
lean_dec(v_a_1583_);
lean_dec_ref(v_e_1574_);
lean_dec(v_idx_1573_);
lean_dec(v_structName_1572_);
return v___x_1631_;
}
}
else
{
lean_dec(v_a_1583_);
lean_dec_ref(v_e_1574_);
lean_dec(v_idx_1573_);
lean_dec(v_structName_1572_);
return v___x_1629_;
}
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_a_1605_);
lean_dec(v_numIndices_1602_);
lean_dec(v_numParams_1601_);
lean_dec_ref(v_toConstantVal_1600_);
lean_dec(v_us_1586_);
v___x_1658_ = lean_box(0);
v___x_1659_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1658_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1659_;
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_numIndices_1602_);
lean_dec(v_numParams_1601_);
lean_dec_ref(v_toConstantVal_1600_);
lean_dec(v_us_1586_);
lean_dec(v_a_1583_);
lean_dec_ref(v_e_1574_);
lean_dec(v_idx_1573_);
lean_dec(v_structName_1572_);
v_a_1660_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1604_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1604_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1598_, 2);
lean_dec_ref(v_val_1597_);
lean_dec(v_us_1586_);
goto v___jp_1588_;
}
}
else
{
lean_dec(v_ctors_1598_);
lean_dec_ref(v_val_1597_);
lean_dec(v_us_1586_);
goto v___jp_1588_;
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_val_1596_);
lean_dec(v_us_1586_);
v___x_1668_ = lean_box(0);
v___x_1669_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1668_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1669_;
}
}
v___jp_1588_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1589_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1590_;
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref(v___x_1584_);
v___x_1670_ = lean_box(0);
v___x_1671_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1583_, lean_box(0), v___x_1670_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1671_;
}
}
else
{
lean_dec_ref(v_e_1574_);
lean_dec(v_idx_1573_);
lean_dec(v_structName_1572_);
return v___x_1582_;
}
}
else
{
lean_dec_ref(v_e_1574_);
lean_dec(v_idx_1573_);
lean_dec(v_structName_1572_);
return v___x_1580_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_0interp(lean_interpreter_value* stack)
{
lean_object* v_structName_1572_ = stack[0].m_obj;
lean_object* v_idx_1573_ = stack[1].m_obj;
lean_object* v_e_1574_ = stack[2].m_obj;
lean_object* v_a_1575_ = stack[3].m_obj;
lean_object* v_a_1576_ = stack[4].m_obj;
lean_object* v_a_1577_ = stack[5].m_obj;
lean_object* v_a_1578_ = stack[6].m_obj;
lean_object* v_res_1672_;
v_res_1672_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1572_, v_idx_1573_, v_e_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
stack->m_obj
 = v_res_1672_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1673_, lean_object* v_idx_1674_, lean_object* v_e_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1673_, v_idx_1674_, v_e_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1681_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1682_, lean_object* v_structName_1683_, lean_object* v_e_1684_, lean_object* v_idx_1685_, lean_object* v_a_1686_, lean_object* v_inst_1687_, lean_object* v_R_1688_, lean_object* v_a_1689_, lean_object* v_b_1690_, lean_object* v_c_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1682_, v_structName_1683_, v_e_1684_, v_idx_1685_, v_a_1686_, v_a_1689_, v_b_1690_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1682_ = stack[0].m_obj;
lean_object* v_structName_1683_ = stack[1].m_obj;
lean_object* v_e_1684_ = stack[2].m_obj;
lean_object* v_idx_1685_ = stack[3].m_obj;
lean_object* v_a_1686_ = stack[4].m_obj;
lean_object* v_a_1689_ = stack[7].m_obj;
lean_object* v_b_1690_ = stack[8].m_obj;
lean_object* v___y_1692_ = stack[10].m_obj;
lean_object* v___y_1693_ = stack[11].m_obj;
lean_object* v___y_1694_ = stack[12].m_obj;
lean_object* v___y_1695_ = stack[13].m_obj;
lean_object* v_res_1698_;
v_res_1698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1682_, v_structName_1683_, v_e_1684_, v_idx_1685_, v_a_1686_, lean_box(0), lean_box(0), v_a_1689_, v_b_1690_, lean_box(0), v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
stack->m_obj
 = v_res_1698_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1699_, lean_object* v_structName_1700_, lean_object* v_e_1701_, lean_object* v_idx_1702_, lean_object* v_a_1703_, lean_object* v_inst_1704_, lean_object* v_R_1705_, lean_object* v_a_1706_, lean_object* v_b_1707_, lean_object* v_c_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1699_, v_structName_1700_, v_e_1701_, v_idx_1702_, v_a_1703_, v_inst_1704_, v_R_1705_, v_a_1706_, v_b_1707_, v_c_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v_upperBound_1699_);
return v_res_1714_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1715_, lean_object* v_structName_1716_, lean_object* v_e_1717_, lean_object* v_idx_1718_, lean_object* v_a_1719_, lean_object* v_inst_1720_, lean_object* v_R_1721_, lean_object* v_a_1722_, lean_object* v_b_1723_, lean_object* v_c_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1715_, v_structName_1716_, v_e_1717_, v_idx_1718_, v_a_1719_, v_a_1722_, v_b_1723_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1715_ = stack[0].m_obj;
lean_object* v_structName_1716_ = stack[1].m_obj;
lean_object* v_e_1717_ = stack[2].m_obj;
lean_object* v_idx_1718_ = stack[3].m_obj;
lean_object* v_a_1719_ = stack[4].m_obj;
lean_object* v_a_1722_ = stack[7].m_obj;
lean_object* v_b_1723_ = stack[8].m_obj;
lean_object* v___y_1725_ = stack[10].m_obj;
lean_object* v___y_1726_ = stack[11].m_obj;
lean_object* v___y_1727_ = stack[12].m_obj;
lean_object* v___y_1728_ = stack[13].m_obj;
lean_object* v_res_1731_;
v_res_1731_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1715_, v_structName_1716_, v_e_1717_, v_idx_1718_, v_a_1719_, lean_box(0), lean_box(0), v_a_1722_, v_b_1723_, lean_box(0), v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
stack->m_obj
 = v_res_1731_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1732_, lean_object* v_structName_1733_, lean_object* v_e_1734_, lean_object* v_idx_1735_, lean_object* v_a_1736_, lean_object* v_inst_1737_, lean_object* v_R_1738_, lean_object* v_a_1739_, lean_object* v_b_1740_, lean_object* v_c_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1732_, v_structName_1733_, v_e_1734_, v_idx_1735_, v_a_1736_, v_inst_1737_, v_R_1738_, v_a_1739_, v_b_1740_, v_c_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v_upperBound_1732_);
return v_res_1747_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1750_ = l_Lean_stringToMessageData(v___x_1749_);
return v___x_1750_;
}
}
lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1758_ = l_Lean_indentExpr(v_type_1751_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1759_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
return v___x_1760_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwTypeExpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1751_ = stack[0].m_obj;
lean_object* v_a_1752_ = stack[1].m_obj;
lean_object* v_a_1753_ = stack[2].m_obj;
lean_object* v_a_1754_ = stack[3].m_obj;
lean_object* v_a_1755_ = stack[4].m_obj;
lean_object* v_res_1761_;
v_res_1761_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
stack->m_obj
 = v_res_1761_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
return v_res_1768_;
}
}
lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1769_, lean_object* v_type_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwTypeExpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1770_ = stack[1].m_obj;
lean_object* v_a_1771_ = stack[2].m_obj;
lean_object* v_a_1772_ = stack[3].m_obj;
lean_object* v_a_1773_ = stack[4].m_obj;
lean_object* v_a_1774_ = stack[5].m_obj;
lean_object* v_res_1777_;
v_res_1777_ = l_Lean_Meta_throwTypeExpected(lean_box(0), v_type_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
stack->m_obj
 = v_res_1777_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_type_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1778_, v_type_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_){
_start:
{
lean_object* v_ks_1790_; lean_object* v_vs_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1815_; 
v_ks_1790_ = lean_ctor_get(v_x_1786_, 0);
v_vs_1791_ = lean_ctor_get(v_x_1786_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_x_1786_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1793_ = v_x_1786_;
v_isShared_1794_ = v_isSharedCheck_1815_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_vs_1791_);
lean_inc(v_ks_1790_);
lean_dec(v_x_1786_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1815_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_array_get_size(v_ks_1790_);
v___x_1796_ = lean_nat_dec_lt(v_x_1787_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
lean_dec(v_x_1787_);
v___x_1797_ = lean_array_push(v_ks_1790_, v_x_1788_);
v___x_1798_ = lean_array_push(v_vs_1791_, v_x_1789_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1798_);
lean_ctor_set(v___x_1793_, 0, v___x_1797_);
v___x_1800_ = v___x_1793_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
else
{
lean_object* v_k_x27_1802_; uint8_t v___x_1803_; 
v_k_x27_1802_ = lean_array_fget_borrowed(v_ks_1790_, v_x_1787_);
v___x_1803_ = l_Lean_instBEqMVarId_beq(v_x_1788_, v_k_x27_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1805_; 
if (v_isShared_1794_ == 0)
{
v___x_1805_ = v___x_1793_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_ks_1790_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_vs_1791_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_nat_add(v_x_1787_, v___x_1806_);
lean_dec(v_x_1787_);
v_x_1786_ = v___x_1805_;
v_x_1787_ = v___x_1807_;
goto _start;
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1810_ = lean_array_fset(v_ks_1790_, v_x_1787_, v_x_1788_);
v___x_1811_ = lean_array_fset(v_vs_1791_, v_x_1787_, v_x_1789_);
lean_dec(v_x_1787_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1811_);
lean_ctor_set(v___x_1793_, 0, v___x_1810_);
v___x_1813_ = v___x_1793_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1816_, lean_object* v_k_1817_, lean_object* v_v_1818_){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1816_, v___x_1819_, v_k_1817_, v_v_1818_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1821_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1822_, size_t v_x_1823_, size_t v_x_1824_, lean_object* v_x_1825_, lean_object* v_x_1826_){
_start:
{
if (lean_obj_tag(v_x_1822_) == 0)
{
lean_object* v_es_1827_; size_t v___x_1828_; size_t v___x_1829_; lean_object* v_j_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_es_1827_ = lean_ctor_get(v_x_1822_, 0);
v___x_1828_ = ((size_t)31ULL);
v___x_1829_ = lean_usize_land(v_x_1823_, v___x_1828_);
v_j_1830_ = lean_usize_to_nat(v___x_1829_);
v___x_1831_ = lean_array_get_size(v_es_1827_);
v___x_1832_ = lean_nat_dec_lt(v_j_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_dec(v_j_1830_);
lean_dec(v_x_1826_);
lean_dec(v_x_1825_);
return v_x_1822_;
}
else
{
lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1871_; 
lean_inc_ref(v_es_1827_);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_x_1822_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v_x_1822_, 0);
lean_dec(v_unused_1872_);
v___x_1834_ = v_x_1822_;
v_isShared_1835_ = v_isSharedCheck_1871_;
goto v_resetjp_1833_;
}
else
{
lean_dec(v_x_1822_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1871_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_v_1836_; lean_object* v___x_1837_; lean_object* v_xs_x27_1838_; lean_object* v___y_1840_; 
v_v_1836_ = lean_array_fget(v_es_1827_, v_j_1830_);
v___x_1837_ = lean_box(0);
v_xs_x27_1838_ = lean_array_fset(v_es_1827_, v_j_1830_, v___x_1837_);
switch(lean_obj_tag(v_v_1836_))
{
case 0:
{
lean_object* v_key_1845_; lean_object* v_val_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1856_; 
v_key_1845_ = lean_ctor_get(v_v_1836_, 0);
v_val_1846_ = lean_ctor_get(v_v_1836_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_v_1836_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1848_ = v_v_1836_;
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_val_1846_);
lean_inc(v_key_1845_);
lean_dec(v_v_1836_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v___x_1850_; 
v___x_1850_ = l_Lean_instBEqMVarId_beq(v_x_1825_, v_key_1845_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_del_object(v___x_1848_);
v___x_1851_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1845_, v_val_1846_, v_x_1825_, v_x_1826_);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
v___y_1840_ = v___x_1852_;
goto v___jp_1839_;
}
else
{
lean_object* v___x_1854_; 
lean_dec(v_val_1846_);
lean_dec(v_key_1845_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v_x_1826_);
lean_ctor_set(v___x_1848_, 0, v_x_1825_);
v___x_1854_ = v___x_1848_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_x_1825_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_x_1826_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
v___y_1840_ = v___x_1854_;
goto v___jp_1839_;
}
}
}
}
case 1:
{
lean_object* v_node_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1869_; 
v_node_1857_ = lean_ctor_get(v_v_1836_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_v_1836_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1859_ = v_v_1836_;
v_isShared_1860_ = v_isSharedCheck_1869_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_node_1857_);
lean_dec(v_v_1836_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1869_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
size_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1861_ = ((size_t)5ULL);
v___x_1862_ = lean_usize_shift_right(v_x_1823_, v___x_1861_);
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_x_1824_, v___x_1863_);
v___x_1865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1857_, v___x_1862_, v___x_1864_, v_x_1825_, v_x_1826_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1865_);
v___x_1867_ = v___x_1859_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
v___y_1840_ = v___x_1867_;
goto v___jp_1839_;
}
}
}
default: 
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_x_1825_);
lean_ctor_set(v___x_1870_, 1, v_x_1826_);
v___y_1840_ = v___x_1870_;
goto v___jp_1839_;
}
}
v___jp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_array_fset(v_xs_x27_1838_, v_j_1830_, v___y_1840_);
lean_dec(v_j_1830_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1841_);
v___x_1843_ = v___x_1834_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
else
{
lean_object* v_ks_1873_; lean_object* v_vs_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1892_; 
v_ks_1873_ = lean_ctor_get(v_x_1822_, 0);
v_vs_1874_ = lean_ctor_get(v_x_1822_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_x_1822_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1876_ = v_x_1822_;
v_isShared_1877_ = v_isSharedCheck_1892_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_vs_1874_);
lean_inc(v_ks_1873_);
lean_dec(v_x_1822_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1892_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_ks_1873_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_vs_1874_);
v___x_1879_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v_newNode_1880_; size_t v___x_1881_; uint8_t v___x_1882_; 
v_newNode_1880_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1879_, v_x_1825_, v_x_1826_);
v___x_1881_ = ((size_t)7ULL);
v___x_1882_ = lean_usize_dec_le(v___x_1881_, v_x_1824_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v___x_1883_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1880_);
v___x_1884_ = lean_unsigned_to_nat(4u);
v___x_1885_ = lean_nat_dec_lt(v___x_1883_, v___x_1884_);
lean_dec(v___x_1883_);
if (v___x_1885_ == 0)
{
lean_object* v_ks_1886_; lean_object* v_vs_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_ks_1886_ = lean_ctor_get(v_newNode_1880_, 0);
lean_inc_ref(v_ks_1886_);
v_vs_1887_ = lean_ctor_get(v_newNode_1880_, 1);
lean_inc_ref(v_vs_1887_);
lean_dec_ref(v_newNode_1880_);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1824_, v_ks_1886_, v_vs_1887_, v___x_1888_, v___x_1889_);
lean_dec_ref(v_vs_1887_);
lean_dec_ref(v_ks_1886_);
return v___x_1890_;
}
else
{
return v_newNode_1880_;
}
}
else
{
return v_newNode_1880_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1822_ = stack[0].m_obj;
size_t v_x_1823_ = stack[1].m_num;
size_t v_x_1824_ = stack[2].m_num;
lean_object* v_x_1825_ = stack[3].m_obj;
lean_object* v_x_1826_ = stack[4].m_obj;
lean_object* v_res_1893_;
v_res_1893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1822_, v_x_1823_, v_x_1824_, v_x_1825_, v_x_1826_);
stack->m_obj
 = v_res_1893_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1894_, lean_object* v_keys_1895_, lean_object* v_vals_1896_, lean_object* v_i_1897_, lean_object* v_entries_1898_){
_start:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_get_size(v_keys_1895_);
v___x_1900_ = lean_nat_dec_lt(v_i_1897_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_dec(v_i_1897_);
return v_entries_1898_;
}
else
{
lean_object* v_k_1901_; lean_object* v_v_1902_; uint64_t v___x_1903_; size_t v_h_1904_; size_t v___x_1905_; lean_object* v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; size_t v_h_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_k_1901_ = lean_array_fget_borrowed(v_keys_1895_, v_i_1897_);
v_v_1902_ = lean_array_fget_borrowed(v_vals_1896_, v_i_1897_);
v___x_1903_ = l_Lean_instHashableMVarId_hash(v_k_1901_);
v_h_1904_ = lean_uint64_to_usize(v___x_1903_);
v___x_1905_ = ((size_t)5ULL);
v___x_1906_ = lean_unsigned_to_nat(1u);
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_sub(v_depth_1894_, v___x_1907_);
v___x_1909_ = lean_usize_mul(v___x_1905_, v___x_1908_);
v_h_1910_ = lean_usize_shift_right(v_h_1904_, v___x_1909_);
v___x_1911_ = lean_nat_add(v_i_1897_, v___x_1906_);
lean_dec(v_i_1897_);
lean_inc(v_v_1902_);
lean_inc(v_k_1901_);
v___x_1912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1898_, v_h_1910_, v_depth_1894_, v_k_1901_, v_v_1902_);
v_i_1897_ = v___x_1911_;
v_entries_1898_ = v___x_1912_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1894_ = stack[0].m_num;
lean_object* v_keys_1895_ = stack[1].m_obj;
lean_object* v_vals_1896_ = stack[2].m_obj;
lean_object* v_i_1897_ = stack[3].m_obj;
lean_object* v_entries_1898_ = stack[4].m_obj;
lean_object* v_res_1914_;
v_res_1914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1894_, v_keys_1895_, v_vals_1896_, v_i_1897_, v_entries_1898_);
stack->m_obj
 = v_res_1914_;
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
size_t v_x_1186__boxed_1927_; size_t v_x_1187__boxed_1928_; lean_object* v_res_1929_; 
v_x_1186__boxed_1927_ = lean_unbox_usize(v_x_1923_);
lean_dec(v_x_1923_);
v_x_1187__boxed_1928_ = lean_unbox_usize(v_x_1924_);
lean_dec(v_x_1924_);
v_res_1929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1922_, v_x_1186__boxed_1927_, v_x_1187__boxed_1928_, v_x_1925_, v_x_1926_);
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
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1937_, lean_object* v_val_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v_mctx_1942_; lean_object* v_cache_1943_; lean_object* v_zetaDeltaFVarIds_1944_; lean_object* v_postponed_1945_; lean_object* v_diag_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1976_; 
v___x_1941_ = lean_st_ref_take(v___y_1939_);
v_mctx_1942_ = lean_ctor_get(v___x_1941_, 0);
v_cache_1943_ = lean_ctor_get(v___x_1941_, 1);
v_zetaDeltaFVarIds_1944_ = lean_ctor_get(v___x_1941_, 2);
v_postponed_1945_ = lean_ctor_get(v___x_1941_, 3);
v_diag_1946_ = lean_ctor_get(v___x_1941_, 4);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1948_ = v___x_1941_;
v_isShared_1949_ = v_isSharedCheck_1976_;
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
v_isShared_1949_ = v_isSharedCheck_1976_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_depth_1950_; lean_object* v_levelAssignDepth_1951_; lean_object* v_lmvarCounter_1952_; lean_object* v_mvarCounter_1953_; lean_object* v_lDecls_1954_; lean_object* v_decls_1955_; lean_object* v_userNames_1956_; lean_object* v_lAssignment_1957_; lean_object* v_eAssignment_1958_; lean_object* v_dAssignment_1959_; lean_object* v_instanceTypedMVars_1960_; lean_object* v_synthNormMemo_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1975_; 
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
v_synthNormMemo_1961_ = lean_ctor_get(v_mctx_1942_, 11);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_mctx_1942_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1963_ = v_mctx_1942_;
v_isShared_1964_ = v_isSharedCheck_1975_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_synthNormMemo_1961_);
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
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1975_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1958_, v_mvarId_1937_, v_val_1938_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 8, v___x_1966_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_depth_1950_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_levelAssignDepth_1951_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_lmvarCounter_1952_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_mvarCounter_1953_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v_lDecls_1954_);
lean_ctor_set(v_reuseFailAlloc_1974_, 5, v_decls_1955_);
lean_ctor_set(v_reuseFailAlloc_1974_, 6, v_userNames_1956_);
lean_ctor_set(v_reuseFailAlloc_1974_, 7, v_lAssignment_1957_);
lean_ctor_set(v_reuseFailAlloc_1974_, 8, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1974_, 9, v_dAssignment_1959_);
lean_ctor_set(v_reuseFailAlloc_1974_, 10, v_instanceTypedMVars_1960_);
lean_ctor_set(v_reuseFailAlloc_1974_, 11, v_synthNormMemo_1961_);
v___x_1968_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1968_);
v___x_1970_ = v___x_1948_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_cache_1943_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_zetaDeltaFVarIds_1944_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_postponed_1945_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_diag_1946_);
v___x_1970_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_st_ref_put(v___y_1939_, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1965_);
return v___x_1972_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1937_ = stack[0].m_obj;
lean_object* v_val_1938_ = stack[1].m_obj;
lean_object* v___y_1939_ = stack[2].m_obj;
lean_object* v_res_1977_;
v_res_1977_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1937_, v_val_1938_, v___y_1939_);
stack->m_obj
 = v_res_1977_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1978_, lean_object* v_val_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1978_, v_val_1979_, v___y_1980_);
lean_dec(v___y_1980_);
return v_res_1982_;
}
}
lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1989_; 
lean_inc(v_a_1987_);
lean_inc_ref(v_a_1986_);
lean_inc(v_a_1985_);
lean_inc_ref(v_a_1984_);
lean_inc_ref(v_type_1983_);
v___x_1989_ = lean_infer_type(v_type_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1991_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v___x_1991_ = l_Lean_Meta_whnfD(v_a_1990_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2026_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2026_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2026_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
switch(lean_obj_tag(v_a_1992_))
{
case 3:
{
lean_object* v_u_1996_; lean_object* v___x_1998_; 
lean_dec_ref(v_type_1983_);
v_u_1996_ = lean_ctor_get(v_a_1992_, 0);
lean_inc(v_u_1996_);
lean_dec_ref_known(v_a_1992_, 1);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_u_1996_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_u_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
case 2:
{
lean_object* v_mvarId_2000_; lean_object* v___x_2001_; 
lean_del_object(v___x_1994_);
v_mvarId_2000_ = lean_ctor_get(v_a_1992_, 0);
lean_inc_n(v_mvarId_2000_, 2);
lean_dec_ref_known(v_a_1992_, 1);
v___x_2001_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_2000_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; uint8_t v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = lean_unbox(v_a_2002_);
lean_dec(v_a_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_dec_ref(v_type_1983_);
v___x_2004_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_n(v_a_2005_, 2);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = l_Lean_mkSort(v_a_2005_);
v___x_2007_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2000_, v___x_2006_, v_a_1985_);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; 
v_unused_2015_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2015_);
v___x_2009_ = v___x_2007_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v___x_2007_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_a_2005_);
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2005_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_dec(v_mvarId_2000_);
return v___x_2004_;
}
}
else
{
lean_object* v___x_2016_; 
lean_dec(v_mvarId_2000_);
v___x_2016_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
return v___x_2016_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_mvarId_2000_);
lean_dec_ref(v_type_1983_);
v_a_2017_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2001_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2001_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
default: 
{
lean_object* v___x_2025_; 
lean_del_object(v___x_1994_);
lean_dec(v_a_1992_);
v___x_2025_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
return v___x_2025_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v_type_1983_);
v_a_2027_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1991_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1991_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_type_1983_);
v_a_2035_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1989_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1989_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1983_ = stack[0].m_obj;
lean_object* v_a_1984_ = stack[1].m_obj;
lean_object* v_a_1985_ = stack[2].m_obj;
lean_object* v_a_1986_ = stack[3].m_obj;
lean_object* v_a_1987_ = stack[4].m_obj;
lean_object* v_res_2043_;
v_res_2043_ = l_Lean_Meta_getLevel(v_type_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
stack->m_obj
 = v_res_2043_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_Meta_getLevel(v_type_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
return v_res_2050_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_2051_, lean_object* v_val_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2051_, v_val_2052_, v___y_2054_);
return v___x_2058_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2051_ = stack[0].m_obj;
lean_object* v_val_2052_ = stack[1].m_obj;
lean_object* v___y_2053_ = stack[2].m_obj;
lean_object* v___y_2054_ = stack[3].m_obj;
lean_object* v___y_2055_ = stack[4].m_obj;
lean_object* v___y_2056_ = stack[5].m_obj;
lean_object* v_res_2059_;
v_res_2059_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_2051_, v_val_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
stack->m_obj
 = v_res_2059_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_2060_, lean_object* v_val_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_2060_, v_val_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_, lean_object* v_x_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2069_, v_x_2070_, v_x_2071_);
return v___x_2072_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2073_, lean_object* v_x_2074_, size_t v_x_2075_, size_t v_x_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2074_, v_x_2075_, v_x_2076_, v_x_2077_, v_x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2074_ = stack[1].m_obj;
size_t v_x_2075_ = stack[2].m_num;
size_t v_x_2076_ = stack[3].m_num;
lean_object* v_x_2077_ = stack[4].m_obj;
lean_object* v_x_2078_ = stack[5].m_obj;
lean_object* v_res_2080_;
v_res_2080_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_box(0), v_x_2074_, v_x_2075_, v_x_2076_, v_x_2077_, v_x_2078_);
stack->m_obj
 = v_res_2080_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
size_t v_x_1720__boxed_2087_; size_t v_x_1721__boxed_2088_; lean_object* v_res_2089_; 
v_x_1720__boxed_2087_ = lean_unbox_usize(v_x_2083_);
lean_dec(v_x_2083_);
v_x_1721__boxed_2088_ = lean_unbox_usize(v_x_2084_);
lean_dec(v_x_2084_);
v_res_2089_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2081_, v_x_2082_, v_x_1720__boxed_2087_, v_x_1721__boxed_2088_, v_x_2085_, v_x_2086_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2090_, lean_object* v_n_2091_, lean_object* v_k_2092_, lean_object* v_v_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2091_, v_k_2092_, v_v_2093_);
return v___x_2094_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2095_, size_t v_depth_2096_, lean_object* v_keys_2097_, lean_object* v_vals_2098_, lean_object* v_heq_2099_, lean_object* v_i_2100_, lean_object* v_entries_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2096_, v_keys_2097_, v_vals_2098_, v_i_2100_, v_entries_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2096_ = stack[1].m_num;
lean_object* v_keys_2097_ = stack[2].m_obj;
lean_object* v_vals_2098_ = stack[3].m_obj;
lean_object* v_i_2100_ = stack[5].m_obj;
lean_object* v_entries_2101_ = stack[6].m_obj;
lean_object* v_res_2103_;
v_res_2103_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_depth_2096_, v_keys_2097_, v_vals_2098_, lean_box(0), v_i_2100_, v_entries_2101_);
stack->m_obj
 = v_res_2103_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2104_, lean_object* v_depth_2105_, lean_object* v_keys_2106_, lean_object* v_vals_2107_, lean_object* v_heq_2108_, lean_object* v_i_2109_, lean_object* v_entries_2110_){
_start:
{
size_t v_depth_boxed_2111_; lean_object* v_res_2112_; 
v_depth_boxed_2111_ = lean_unbox_usize(v_depth_2105_);
lean_dec(v_depth_2105_);
v_res_2112_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2104_, v_depth_boxed_2111_, v_keys_2106_, v_vals_2107_, v_heq_2108_, v_i_2109_, v_entries_2110_);
lean_dec_ref(v_vals_2107_);
lean_dec_ref(v_keys_2106_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2114_, v_x_2115_, v_x_2116_, v_x_2117_);
return v___x_2118_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2119_, lean_object* v_b_2120_, lean_object* v_c_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
lean_inc(v___y_2125_);
lean_inc_ref(v___y_2124_);
lean_inc(v___y_2123_);
lean_inc_ref(v___y_2122_);
v___x_2127_ = lean_apply_7(v_k_2119_, v_b_2120_, v_c_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, lean_box(0));
return v___x_2127_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2119_ = stack[0].m_obj;
lean_object* v_b_2120_ = stack[1].m_obj;
lean_object* v_c_2121_ = stack[2].m_obj;
lean_object* v___y_2122_ = stack[3].m_obj;
lean_object* v___y_2123_ = stack[4].m_obj;
lean_object* v___y_2124_ = stack[5].m_obj;
lean_object* v___y_2125_ = stack[6].m_obj;
lean_object* v_res_2128_;
v_res_2128_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2119_, v_b_2120_, v_c_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
stack->m_obj
 = v_res_2128_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2129_, lean_object* v_b_2130_, lean_object* v_c_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2129_, v_b_2130_, v_c_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2137_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2138_, lean_object* v_k_2139_, uint8_t v_cleanupAnnotations_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___f_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___f_2146_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2146_, 0, v_k_2139_);
v___x_2147_ = 0;
v___x_2148_ = lean_box(0);
v___x_2149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2147_, v___x_2148_, v_type_2138_, v___f_2146_, v_cleanupAnnotations_2140_, v___x_2147_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
v_a_2158_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2149_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2149_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2138_ = stack[0].m_obj;
lean_object* v_k_2139_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2140_ = stack[2].m_num;
lean_object* v___y_2141_ = stack[3].m_obj;
lean_object* v___y_2142_ = stack[4].m_obj;
lean_object* v___y_2143_ = stack[5].m_obj;
lean_object* v___y_2144_ = stack[6].m_obj;
lean_object* v_res_2166_;
v_res_2166_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2138_, v_k_2139_, v_cleanupAnnotations_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
stack->m_obj
 = v_res_2166_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2167_, lean_object* v_k_2168_, lean_object* v_cleanupAnnotations_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2175_; lean_object* v_res_2176_; 
v_cleanupAnnotations_boxed_2175_ = lean_unbox(v_cleanupAnnotations_2169_);
v_res_2176_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2167_, v_k_2168_, v_cleanupAnnotations_boxed_2175_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2176_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2177_, lean_object* v_type_2178_, lean_object* v_k_2179_, uint8_t v_cleanupAnnotations_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2178_, v_k_2179_, v_cleanupAnnotations_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2178_ = stack[1].m_obj;
lean_object* v_k_2179_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2180_ = stack[3].m_num;
lean_object* v___y_2181_ = stack[4].m_obj;
lean_object* v___y_2182_ = stack[5].m_obj;
lean_object* v___y_2183_ = stack[6].m_obj;
lean_object* v___y_2184_ = stack[7].m_obj;
lean_object* v_res_2187_;
v_res_2187_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_box(0), v_type_2178_, v_k_2179_, v_cleanupAnnotations_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
stack->m_obj
 = v_res_2187_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2188_, lean_object* v_type_2189_, lean_object* v_k_2190_, lean_object* v_cleanupAnnotations_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2197_; lean_object* v_res_2198_; 
v_cleanupAnnotations_boxed_2197_ = lean_unbox(v_cleanupAnnotations_2191_);
v_res_2198_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2188_, v_type_2189_, v_k_2190_, v_cleanupAnnotations_boxed_2197_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v_res_2198_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2199_, size_t v_i_2200_, size_t v_stop_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = lean_usize_dec_eq(v_i_2200_, v_stop_2201_);
if (v___x_2208_ == 0)
{
size_t v___x_2209_; size_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2209_ = ((size_t)1ULL);
v___x_2210_ = lean_usize_sub(v_i_2200_, v___x_2209_);
v___x_2211_ = lean_array_uget_borrowed(v_as_2199_, v___x_2210_);
lean_inc(v___y_2206_);
lean_inc_ref(v___y_2205_);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___x_2211_);
v___x_2212_ = lean_infer_type(v___x_2211_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = l_Lean_Meta_getLevel(v_a_2213_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = l_Lean_mkLevelIMax_x27(v_a_2215_, v_b_2202_);
v_i_2200_ = v___x_2210_;
v_b_2202_ = v___x_2216_;
goto _start;
}
else
{
lean_dec(v_b_2202_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2218_; 
v_a_2218_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2214_, 1);
v_i_2200_ = v___x_2210_;
v_b_2202_ = v_a_2218_;
goto _start;
}
else
{
return v___x_2214_;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_b_2202_);
v_a_2220_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2212_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2212_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v_b_2202_);
return v___x_2228_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2199_ = stack[0].m_obj;
size_t v_i_2200_ = stack[1].m_num;
size_t v_stop_2201_ = stack[2].m_num;
lean_object* v_b_2202_ = stack[3].m_obj;
lean_object* v___y_2203_ = stack[4].m_obj;
lean_object* v___y_2204_ = stack[5].m_obj;
lean_object* v___y_2205_ = stack[6].m_obj;
lean_object* v___y_2206_ = stack[7].m_obj;
lean_object* v_res_2229_;
v_res_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2199_, v_i_2200_, v_stop_2201_, v_b_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
stack->m_obj
 = v_res_2229_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2230_, lean_object* v_i_2231_, lean_object* v_stop_2232_, lean_object* v_b_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
size_t v_i_boxed_2239_; size_t v_stop_boxed_2240_; lean_object* v_res_2241_; 
v_i_boxed_2239_ = lean_unbox_usize(v_i_2231_);
lean_dec(v_i_2231_);
v_stop_boxed_2240_ = lean_unbox_usize(v_stop_2232_);
lean_dec(v_stop_2232_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2230_, v_i_boxed_2239_, v_stop_boxed_2240_, v_b_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v_as_2230_);
return v_res_2241_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2242_, lean_object* v_e_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___y_2250_; lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Meta_getLevel(v_e_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v___x_2271_ = lean_array_get_size(v_xs_2242_);
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = lean_nat_dec_lt(v___x_2272_, v___x_2271_);
if (v___x_2273_ == 0)
{
v___y_2250_ = v___x_2269_;
goto v___jp_2249_;
}
else
{
size_t v___x_2274_; size_t v___x_2275_; lean_object* v___x_2276_; 
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2274_ = lean_usize_of_nat(v___x_2271_);
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2242_, v___x_2274_, v___x_2275_, v_a_2270_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
v___y_2250_ = v___x_2276_;
goto v___jp_2249_;
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_a_2277_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2269_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2269_);
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
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2249_:
{
if (lean_obj_tag(v___y_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2260_; 
v_a_2251_ = lean_ctor_get(v___y_2250_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___y_2250_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2253_ = v___y_2250_;
v_isShared_2254_ = v_isSharedCheck_2260_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___y_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2260_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2255_ = l_Lean_Level_normalize(v_a_2251_);
lean_dec(v_a_2251_);
v___x_2256_ = l_Lean_mkSort(v___x_2255_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2256_);
v___x_2258_ = v___x_2253_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2261_ = lean_ctor_get(v___y_2250_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___y_2250_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___y_2250_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___y_2250_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2242_ = stack[0].m_obj;
lean_object* v_e_2243_ = stack[1].m_obj;
lean_object* v___y_2244_ = stack[2].m_obj;
lean_object* v___y_2245_ = stack[3].m_obj;
lean_object* v___y_2246_ = stack[4].m_obj;
lean_object* v___y_2247_ = stack[5].m_obj;
lean_object* v_res_2285_;
v_res_2285_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2242_, v_e_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
stack->m_obj
 = v_res_2285_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2286_, lean_object* v_e_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2286_, v_e_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v_xs_2286_);
return v_res_2293_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___f_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
v___f_2301_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2302_ = 0;
v___x_2303_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2295_, v___f_2301_, v___x_2302_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2303_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2295_ = stack[0].m_obj;
lean_object* v_a_2296_ = stack[1].m_obj;
lean_object* v_a_2297_ = stack[2].m_obj;
lean_object* v_a_2298_ = stack[3].m_obj;
lean_object* v_a_2299_ = stack[4].m_obj;
lean_object* v_res_2304_;
v_res_2304_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
stack->m_obj
 = v_res_2304_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2311_;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2312_, lean_object* v_k_2313_, uint8_t v_cleanupAnnotations_2314_, uint8_t v_preserveNondepLet_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___f_2321_; uint8_t v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___f_2321_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2321_, 0, v_k_2313_);
v___x_2322_ = 1;
v___x_2323_ = 0;
v___x_2324_ = lean_box(0);
v___x_2325_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2312_, v___x_2322_, v___x_2322_, v_preserveNondepLet_2315_, v___x_2323_, v___x_2324_, v___f_2321_, v_cleanupAnnotations_2314_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2325_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2325_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2312_ = stack[0].m_obj;
lean_object* v_k_2313_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2314_ = stack[2].m_num;
uint8_t v_preserveNondepLet_2315_ = stack[3].m_num;
lean_object* v___y_2316_ = stack[4].m_obj;
lean_object* v___y_2317_ = stack[5].m_obj;
lean_object* v___y_2318_ = stack[6].m_obj;
lean_object* v___y_2319_ = stack[7].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2312_, v_k_2313_, v_cleanupAnnotations_2314_, v_preserveNondepLet_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2343_, lean_object* v_k_2344_, lean_object* v_cleanupAnnotations_2345_, lean_object* v_preserveNondepLet_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2352_; uint8_t v_preserveNondepLet_boxed_2353_; lean_object* v_res_2354_; 
v_cleanupAnnotations_boxed_2352_ = lean_unbox(v_cleanupAnnotations_2345_);
v_preserveNondepLet_boxed_2353_ = lean_unbox(v_preserveNondepLet_2346_);
v_res_2354_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2343_, v_k_2344_, v_cleanupAnnotations_boxed_2352_, v_preserveNondepLet_boxed_2353_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2354_;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2355_, lean_object* v_e_2356_, lean_object* v_k_2357_, uint8_t v_cleanupAnnotations_2358_, uint8_t v_preserveNondepLet_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2356_, v_k_2357_, v_cleanupAnnotations_2358_, v_preserveNondepLet_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2365_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2356_ = stack[1].m_obj;
lean_object* v_k_2357_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2358_ = stack[3].m_num;
uint8_t v_preserveNondepLet_2359_ = stack[4].m_num;
lean_object* v___y_2360_ = stack[5].m_obj;
lean_object* v___y_2361_ = stack[6].m_obj;
lean_object* v___y_2362_ = stack[7].m_obj;
lean_object* v___y_2363_ = stack[8].m_obj;
lean_object* v_res_2366_;
v_res_2366_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_box(0), v_e_2356_, v_k_2357_, v_cleanupAnnotations_2358_, v_preserveNondepLet_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
stack->m_obj
 = v_res_2366_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_e_2368_, lean_object* v_k_2369_, lean_object* v_cleanupAnnotations_2370_, lean_object* v_preserveNondepLet_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2377_; uint8_t v_preserveNondepLet_boxed_2378_; lean_object* v_res_2379_; 
v_cleanupAnnotations_boxed_2377_ = lean_unbox(v_cleanupAnnotations_2370_);
v_preserveNondepLet_boxed_2378_ = lean_unbox(v_preserveNondepLet_2371_);
v_res_2379_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2367_, v_e_2368_, v_k_2369_, v_cleanupAnnotations_boxed_2377_, v_preserveNondepLet_boxed_2378_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2379_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2380_, lean_object* v_e_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; 
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc(v___y_2383_);
lean_inc_ref(v___y_2382_);
v___x_2387_ = lean_infer_type(v_e_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; uint8_t v___x_2389_; uint8_t v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = 0;
v___x_2390_ = 1;
v___x_2391_ = 1;
v___x_2392_ = l_Lean_Meta_mkForallFVars(v_xs_2380_, v_a_2388_, v___x_2389_, v___x_2390_, v___x_2389_, v___x_2391_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2392_;
}
else
{
return v___x_2387_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2380_ = stack[0].m_obj;
lean_object* v_e_2381_ = stack[1].m_obj;
lean_object* v___y_2382_ = stack[2].m_obj;
lean_object* v___y_2383_ = stack[3].m_obj;
lean_object* v___y_2384_ = stack[4].m_obj;
lean_object* v___y_2385_ = stack[5].m_obj;
lean_object* v_res_2393_;
v_res_2393_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2380_, v_e_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
stack->m_obj
 = v_res_2393_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2394_, lean_object* v_e_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2394_, v_e_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v_xs_2394_);
return v_res_2401_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___f_2409_; uint8_t v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; 
v___f_2409_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2410_ = 0;
v___x_2411_ = 1;
v___x_2412_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2403_, v___f_2409_, v___x_2410_, v___x_2411_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
return v___x_2412_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2403_ = stack[0].m_obj;
lean_object* v_a_2404_ = stack[1].m_obj;
lean_object* v_a_2405_ = stack[2].m_obj;
lean_object* v_a_2406_ = stack[3].m_obj;
lean_object* v_a_2407_ = stack[4].m_obj;
lean_object* v_res_2413_;
v_res_2413_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
stack->m_obj
 = v_res_2413_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2420_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2433_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2434_ = l_Lean_MessageData_ofName(v_mvarId_2427_);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2437_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
return v___x_2438_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwUnknownMVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2427_ = stack[0].m_obj;
lean_object* v_a_2428_ = stack[1].m_obj;
lean_object* v_a_2429_ = stack[2].m_obj;
lean_object* v_a_2430_ = stack[3].m_obj;
lean_object* v_a_2431_ = stack[4].m_obj;
lean_object* v_res_2439_;
v_res_2439_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
stack->m_obj
 = v_res_2439_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
return v_res_2446_;
}
}
lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2447_, lean_object* v_mvarId_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT void l_Lean_Meta_throwUnknownMVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2448_ = stack[1].m_obj;
lean_object* v_a_2449_ = stack[2].m_obj;
lean_object* v_a_2450_ = stack[3].m_obj;
lean_object* v_a_2451_ = stack[4].m_obj;
lean_object* v_a_2452_ = stack[5].m_obj;
lean_object* v_res_2455_;
v_res_2455_ = l_Lean_Meta_throwUnknownMVar(lean_box(0), v_mvarId_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
stack->m_obj
 = v_res_2455_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_mvarId_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2456_, v_mvarId_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
return v_res_2463_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v___x_2470_; lean_object* v_mctx_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_st_ref_get(v_a_2466_);
v_mctx_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc_ref(v_mctx_2471_);
lean_dec(v___x_2470_);
v___x_2472_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2471_, v_mvarId_2464_);
lean_dec_ref(v_mctx_2471_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
return v___x_2473_;
}
else
{
lean_object* v_val_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_mvarId_2464_);
v_val_2474_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2476_ = v___x_2472_;
v_isShared_2477_ = v_isSharedCheck_2482_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_val_2474_);
lean_dec(v___x_2472_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2482_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v_type_2478_; lean_object* v___x_2480_; 
v_type_2478_ = lean_ctor_get(v_val_2474_, 2);
lean_inc_ref(v_type_2478_);
lean_dec(v_val_2474_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set_tag(v___x_2476_, 0);
lean_ctor_set(v___x_2476_, 0, v_type_2478_);
v___x_2480_ = v___x_2476_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_type_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2464_ = stack[0].m_obj;
lean_object* v_a_2465_ = stack[1].m_obj;
lean_object* v_a_2466_ = stack[2].m_obj;
lean_object* v_a_2467_ = stack[3].m_obj;
lean_object* v_a_2468_ = stack[4].m_obj;
lean_object* v_res_2483_;
v_res_2483_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
stack->m_obj
 = v_res_2483_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
return v_res_2490_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_lctx_2496_; lean_object* v___x_2497_; 
v_lctx_2496_ = lean_ctor_get(v_a_2492_, 2);
lean_inc(v_fvarId_2491_);
lean_inc_ref(v_lctx_2496_);
v___x_2497_ = lean_local_ctx_find(v_lctx_2496_, v_fvarId_2491_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2491_, v_a_2493_, v_a_2494_);
return v___x_2498_;
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_fvarId_2491_);
v_val_2499_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2507_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_val_2499_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2507_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = l_Lean_LocalDecl_type(v_val_2499_);
lean_dec(v_val_2499_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2503_);
v___x_2505_ = v___x_2501_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2491_ = stack[0].m_obj;
lean_object* v_a_2492_ = stack[1].m_obj;
lean_object* v_a_2493_ = stack[2].m_obj;
lean_object* v_a_2494_ = stack[3].m_obj;
lean_object* v_res_2508_;
v_res_2508_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
stack->m_obj
 = v_res_2508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec_ref(v_a_2510_);
return v_res_2514_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2515_, v_a_2516_, v_a_2518_, v_a_2519_);
return v___x_2521_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_2515_ = stack[0].m_obj;
lean_object* v_a_2516_ = stack[1].m_obj;
lean_object* v_a_2517_ = stack[2].m_obj;
lean_object* v_a_2518_ = stack[3].m_obj;
lean_object* v_a_2519_ = stack[4].m_obj;
lean_object* v_res_2522_;
v_res_2522_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
stack->m_obj
 = v_res_2522_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
return v_res_2529_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_instMonadEIO___redArg();
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2532_ = l_StateRefT_x27_instMonad___redArg(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_instMonadExceptOfEIO___redArg();
return v___x_2535_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___f_2537_; 
v___x_2536_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2537_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2537_, 0, v___x_2536_);
return v___f_2537_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___f_2539_; 
v___x_2538_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2539_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2539_, 0, v___x_2538_);
return v___f_2539_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; 
v___f_2540_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2541_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___f_2541_);
lean_ctor_set(v___x_2542_, 1, v___f_2540_);
return v___x_2542_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___f_2544_; 
v___x_2543_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2544_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2544_, 0, v___x_2543_);
return v___f_2544_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___f_2546_; 
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2546_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2546_, 0, v___x_2545_);
return v___f_2546_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2547_; lean_object* v___f_2548_; lean_object* v___x_2549_; 
v___f_2547_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2548_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___f_2548_);
lean_ctor_set(v___x_2549_, 1, v___f_2547_);
return v___x_2549_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2552_, lean_object* v_inferType_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
uint8_t v_cacheInferType_2598_; 
v_cacheInferType_2598_ = lean_ctor_get_uint8(v_a_2554_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2598_ == 0)
{
lean_dec_ref(v_e_2552_);
goto v___jp_2559_;
}
else
{
uint8_t v___x_2599_; 
v___x_2599_ = l_Lean_Expr_hasMVar(v_e_2552_);
if (v___x_2599_ == 0)
{
lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___f_2600_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2601_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2602_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2552_, v_a_2554_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2700_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2700_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2700_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2647_; lean_object* v_cache_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2695_; 
v___x_2647_ = lean_st_ref_get(v_a_2555_);
v_cache_2648_ = lean_ctor_get(v___x_2647_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; lean_object* v_unused_2697_; lean_object* v_unused_2698_; lean_object* v_unused_2699_; 
v_unused_2696_ = lean_ctor_get(v___x_2647_, 4);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v___x_2647_, 3);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v___x_2647_, 2);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v___x_2647_, 0);
lean_dec(v_unused_2699_);
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2695_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_cache_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2695_;
goto v_resetjp_2649_;
}
v___jp_2607_:
{
lean_object* v___x_2608_; 
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
lean_inc(v_a_2555_);
lean_inc_ref(v_a_2554_);
v___x_2608_ = lean_apply_5(v_inferType_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, lean_box(0));
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; uint8_t v___x_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
v___x_2610_ = l_Lean_Expr_hasMVar(v_a_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2645_; 
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v___x_2608_, 0);
lean_dec(v_unused_2646_);
v___x_2612_ = v___x_2608_;
v_isShared_2613_ = v_isSharedCheck_2645_;
goto v_resetjp_2611_;
}
else
{
lean_dec(v___x_2608_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2645_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v_cache_2615_; lean_object* v_mctx_2616_; lean_object* v_zetaDeltaFVarIds_2617_; lean_object* v_postponed_2618_; lean_object* v_diag_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2644_; 
v___x_2614_ = lean_st_ref_take(v_a_2555_);
v_cache_2615_ = lean_ctor_get(v___x_2614_, 1);
v_mctx_2616_ = lean_ctor_get(v___x_2614_, 0);
v_zetaDeltaFVarIds_2617_ = lean_ctor_get(v___x_2614_, 2);
v_postponed_2618_ = lean_ctor_get(v___x_2614_, 3);
v_diag_2619_ = lean_ctor_get(v___x_2614_, 4);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2621_ = v___x_2614_;
v_isShared_2622_ = v_isSharedCheck_2644_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_diag_2619_);
lean_inc(v_postponed_2618_);
lean_inc(v_zetaDeltaFVarIds_2617_);
lean_inc(v_cache_2615_);
lean_inc(v_mctx_2616_);
lean_dec(v___x_2614_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2644_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v_inferType_2623_; lean_object* v_funInfo_2624_; lean_object* v_synthInstance_2625_; lean_object* v_whnf_2626_; lean_object* v_defEqTrans_2627_; lean_object* v_defEqPerm_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2643_; 
v_inferType_2623_ = lean_ctor_get(v_cache_2615_, 0);
v_funInfo_2624_ = lean_ctor_get(v_cache_2615_, 1);
v_synthInstance_2625_ = lean_ctor_get(v_cache_2615_, 2);
v_whnf_2626_ = lean_ctor_get(v_cache_2615_, 3);
v_defEqTrans_2627_ = lean_ctor_get(v_cache_2615_, 4);
v_defEqPerm_2628_ = lean_ctor_get(v_cache_2615_, 5);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_cache_2615_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2630_ = v_cache_2615_;
v_isShared_2631_ = v_isSharedCheck_2643_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_defEqPerm_2628_);
lean_inc(v_defEqTrans_2627_);
lean_inc(v_whnf_2626_);
lean_inc(v_synthInstance_2625_);
lean_inc(v_funInfo_2624_);
lean_inc(v_inferType_2623_);
lean_dec(v_cache_2615_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2643_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_inc(v_a_2609_);
v___x_2632_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2600_, v___x_2601_, v_inferType_2623_, v_a_2603_, v_a_2609_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_funInfo_2624_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_synthInstance_2625_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_whnf_2626_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v_defEqTrans_2627_);
lean_ctor_set(v_reuseFailAlloc_2642_, 5, v_defEqPerm_2628_);
v___x_2634_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 1, v___x_2634_);
v___x_2636_ = v___x_2621_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_mctx_2616_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_zetaDeltaFVarIds_2617_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_postponed_2618_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_diag_2619_);
v___x_2636_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = lean_st_ref_put(v_a_2555_, v___x_2636_);
if (v_isShared_2613_ == 0)
{
v___x_2639_ = v___x_2612_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2609_);
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
}
}
else
{
lean_dec(v_a_2609_);
lean_dec(v_a_2603_);
return v___x_2608_;
}
}
else
{
lean_dec(v_a_2603_);
return v___x_2608_;
}
}
v_resetjp_2649_:
{
lean_object* v_inferType_2652_; lean_object* v___x_2653_; 
v_inferType_2652_ = lean_ctor_get(v_cache_2648_, 0);
lean_inc_ref(v_inferType_2652_);
lean_dec_ref(v_cache_2648_);
lean_inc(v_a_2603_);
v___x_2653_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2600_, v___x_2601_, v_inferType_2652_, v_a_2603_);
lean_dec_ref(v_inferType_2652_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v___x_2654_; lean_object* v_toApplicative_2655_; lean_object* v_toFunctor_2656_; lean_object* v_toSeq_2657_; lean_object* v_toSeqLeft_2658_; lean_object* v_toSeqRight_2659_; lean_object* v___f_2660_; lean_object* v___f_2661_; lean_object* v___f_2662_; lean_object* v___f_2663_; lean_object* v___x_2664_; lean_object* v___f_2665_; lean_object* v___f_2666_; lean_object* v___f_2667_; lean_object* v___x_2669_; 
lean_del_object(v___x_2605_);
v___x_2654_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2655_ = lean_ctor_get(v___x_2654_, 0);
v_toFunctor_2656_ = lean_ctor_get(v_toApplicative_2655_, 0);
v_toSeq_2657_ = lean_ctor_get(v_toApplicative_2655_, 2);
v_toSeqLeft_2658_ = lean_ctor_get(v_toApplicative_2655_, 3);
v_toSeqRight_2659_ = lean_ctor_get(v_toApplicative_2655_, 4);
v___f_2660_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2661_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2656_, 2);
v___f_2662_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2662_, 0, v_toFunctor_2656_);
v___f_2663_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2663_, 0, v_toFunctor_2656_);
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___f_2662_);
lean_ctor_set(v___x_2664_, 1, v___f_2663_);
lean_inc(v_toSeqRight_2659_);
v___f_2665_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2665_, 0, v_toSeqRight_2659_);
lean_inc(v_toSeqLeft_2658_);
v___f_2666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2666_, 0, v_toSeqLeft_2658_);
lean_inc(v_toSeq_2657_);
v___f_2667_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2667_, 0, v_toSeq_2657_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 4, v___f_2665_);
lean_ctor_set(v___x_2650_, 3, v___f_2666_);
lean_ctor_set(v___x_2650_, 2, v___f_2667_);
lean_ctor_set(v___x_2650_, 1, v___f_2660_);
lean_ctor_set(v___x_2650_, 0, v___x_2664_);
v___x_2669_ = v___x_2650_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___f_2660_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v___f_2667_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v___f_2666_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v___f_2665_);
v___x_2669_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_toCold_2676_; lean_object* v_cancelTk_x3f_2677_; 
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___f_2661_);
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2672_ = l_Lean_Core_instMonadRefCoreM;
v___x_2673_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2674_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2673_, v___x_2670_);
v___x_2675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2671_);
lean_ctor_set(v___x_2675_, 1, v___x_2672_);
lean_ctor_set(v___x_2675_, 2, v___x_2674_);
v_toCold_2676_ = lean_ctor_get(v_a_2556_, 0);
v_cancelTk_x3f_2677_ = lean_ctor_get(v_toCold_2676_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2677_) == 1)
{
lean_object* v_val_2678_; uint8_t v___x_2679_; 
v_val_2678_ = lean_ctor_get(v_cancelTk_x3f_2677_, 0);
v___x_2679_ = l_IO_CancelToken_isSet(v_val_2678_);
if (v___x_2679_ == 0)
{
lean_dec_ref_known(v___x_2675_, 3);
goto v___jp_2607_;
}
else
{
lean_object* v___x_2058__overap_2680_; lean_object* v___x_2681_; 
v___x_2058__overap_2680_ = l_Lean_throwInterruptException___redArg(v___x_2675_);
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
v___x_2681_ = lean_apply_3(v___x_2058__overap_2680_, v_a_2556_, v_a_2557_, lean_box(0));
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec_ref_known(v___x_2681_, 1);
goto v___jp_2607_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_a_2603_);
lean_dec_ref(v_inferType_2553_);
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2675_, 3);
goto v___jp_2607_;
}
}
}
else
{
lean_object* v_val_2691_; lean_object* v___x_2693_; 
lean_del_object(v___x_2650_);
lean_dec(v_a_2603_);
lean_dec_ref(v_inferType_2553_);
v_val_2691_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_val_2691_);
lean_dec_ref_known(v___x_2653_, 1);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v_val_2691_);
v___x_2693_ = v___x_2605_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_val_2691_);
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
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v_inferType_2553_);
v_a_2701_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2602_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2602_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_dec_ref(v_e_2552_);
goto v___jp_2559_;
}
}
v___jp_2559_:
{
lean_object* v___x_2560_; lean_object* v_toApplicative_2561_; lean_object* v_toFunctor_2562_; lean_object* v_toSeq_2563_; lean_object* v_toSeqLeft_2564_; lean_object* v_toSeqRight_2565_; lean_object* v___f_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v_toCold_2581_; lean_object* v_cancelTk_x3f_2582_; 
v___x_2560_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2561_ = lean_ctor_get(v___x_2560_, 0);
v_toFunctor_2562_ = lean_ctor_get(v_toApplicative_2561_, 0);
v_toSeq_2563_ = lean_ctor_get(v_toApplicative_2561_, 2);
v_toSeqLeft_2564_ = lean_ctor_get(v_toApplicative_2561_, 3);
v_toSeqRight_2565_ = lean_ctor_get(v_toApplicative_2561_, 4);
v___f_2566_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2567_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2562_, 2);
v___f_2568_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2568_, 0, v_toFunctor_2562_);
v___f_2569_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2569_, 0, v_toFunctor_2562_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___f_2568_);
lean_ctor_set(v___x_2570_, 1, v___f_2569_);
lean_inc(v_toSeqRight_2565_);
v___f_2571_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2571_, 0, v_toSeqRight_2565_);
lean_inc(v_toSeqLeft_2564_);
v___f_2572_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2572_, 0, v_toSeqLeft_2564_);
lean_inc(v_toSeq_2563_);
v___f_2573_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2573_, 0, v_toSeq_2563_);
v___x_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2570_);
lean_ctor_set(v___x_2574_, 1, v___f_2566_);
lean_ctor_set(v___x_2574_, 2, v___f_2573_);
lean_ctor_set(v___x_2574_, 3, v___f_2572_);
lean_ctor_set(v___x_2574_, 4, v___f_2571_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___f_2567_);
v___x_2576_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2577_ = l_Lean_Core_instMonadRefCoreM;
v___x_2578_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2579_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2578_, v___x_2575_);
v___x_2580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2576_);
lean_ctor_set(v___x_2580_, 1, v___x_2577_);
lean_ctor_set(v___x_2580_, 2, v___x_2579_);
v_toCold_2581_ = lean_ctor_get(v_a_2556_, 0);
v_cancelTk_x3f_2582_ = lean_ctor_get(v_toCold_2581_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2582_) == 1)
{
lean_object* v_val_2583_; uint8_t v___x_2584_; 
v_val_2583_ = lean_ctor_get(v_cancelTk_x3f_2582_, 0);
v___x_2584_ = l_IO_CancelToken_isSet(v_val_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
lean_dec_ref_known(v___x_2580_, 3);
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
lean_inc(v_a_2555_);
lean_inc_ref(v_a_2554_);
v___x_2585_ = lean_apply_5(v_inferType_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, lean_box(0));
return v___x_2585_;
}
else
{
lean_object* v___x_2031__overap_2586_; lean_object* v___x_2587_; 
v___x_2031__overap_2586_ = l_Lean_throwInterruptException___redArg(v___x_2580_);
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
v___x_2587_ = lean_apply_3(v___x_2031__overap_2586_, v_a_2556_, v_a_2557_, lean_box(0));
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref_known(v___x_2587_, 1);
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
lean_inc(v_a_2555_);
lean_inc_ref(v_a_2554_);
v___x_2588_ = lean_apply_5(v_inferType_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, lean_box(0));
return v___x_2588_;
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_inferType_2553_);
v_a_2589_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2587_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2587_);
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
}
else
{
lean_object* v___x_2597_; 
lean_dec_ref_known(v___x_2580_, 3);
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
lean_inc(v_a_2555_);
lean_inc_ref(v_a_2554_);
v___x_2597_ = lean_apply_5(v_inferType_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, lean_box(0));
return v___x_2597_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2552_ = stack[0].m_obj;
lean_object* v_inferType_2553_ = stack[1].m_obj;
lean_object* v_a_2554_ = stack[2].m_obj;
lean_object* v_a_2555_ = stack[3].m_obj;
lean_object* v_a_2556_ = stack[4].m_obj;
lean_object* v_a_2557_ = stack[5].m_obj;
lean_object* v_res_2709_;
v_res_2709_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2552_, v_inferType_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
stack->m_obj
 = v_res_2709_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2710_, lean_object* v_inferType_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2710_, v_inferType_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2717_;
}
}
lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2770_; uint8_t v_beta_2771_; 
v___x_2770_ = l_Lean_Meta_Context_config(v___y_2719_);
v_beta_2771_ = lean_ctor_get_uint8(v___x_2770_, 13);
if (v_beta_2771_ == 0)
{
lean_dec_ref(v___x_2770_);
goto v___jp_2724_;
}
else
{
uint8_t v_iota_2772_; 
v_iota_2772_ = lean_ctor_get_uint8(v___x_2770_, 12);
if (v_iota_2772_ == 0)
{
lean_dec_ref(v___x_2770_);
goto v___jp_2724_;
}
else
{
uint8_t v_zeta_2773_; 
v_zeta_2773_ = lean_ctor_get_uint8(v___x_2770_, 15);
if (v_zeta_2773_ == 0)
{
lean_dec_ref(v___x_2770_);
goto v___jp_2724_;
}
else
{
uint8_t v_zetaHave_2774_; 
v_zetaHave_2774_ = lean_ctor_get_uint8(v___x_2770_, 18);
if (v_zetaHave_2774_ == 0)
{
lean_dec_ref(v___x_2770_);
goto v___jp_2724_;
}
else
{
uint8_t v_zetaDelta_2775_; 
v_zetaDelta_2775_ = lean_ctor_get_uint8(v___x_2770_, 16);
if (v_zetaDelta_2775_ == 0)
{
lean_dec_ref(v___x_2770_);
goto v___jp_2724_;
}
else
{
uint8_t v_etaStruct_2776_; uint8_t v_proj_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v_etaStruct_2776_ = lean_ctor_get_uint8(v___x_2770_, 10);
v_proj_2777_ = lean_ctor_get_uint8(v___x_2770_, 14);
lean_dec_ref(v___x_2770_);
v___x_2778_ = lean_box(v_proj_2777_);
v___x_2779_ = lean_obj_tag_nat(v___x_2778_);
lean_dec(v___x_2778_);
v___x_2780_ = lean_unsigned_to_nat(2u);
v___x_2781_ = lean_nat_dec_eq(v___x_2779_, v___x_2780_);
if (v___x_2781_ == 0)
{
goto v___jp_2724_;
}
else
{
uint8_t v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = 0;
v___x_2783_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2776_, v___x_2782_);
if (v___x_2783_ == 0)
{
goto v___jp_2724_;
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_apply_5(v_x_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
return v___x_2784_;
}
}
}
}
}
}
}
v___jp_2724_:
{
lean_object* v___x_2725_; uint8_t v_foApprox_2726_; uint8_t v_ctxApprox_2727_; uint8_t v_quasiPatternApprox_2728_; uint8_t v_constApprox_2729_; uint8_t v_isDefEqStuckEx_2730_; uint8_t v_unificationHints_2731_; uint8_t v_proofIrrelevance_2732_; uint8_t v_assignSyntheticOpaque_2733_; uint8_t v_offsetCnstrs_2734_; uint8_t v_transparency_2735_; uint8_t v_univApprox_2736_; uint8_t v_zetaUnused_2737_; uint8_t v_canUnfoldPredicateConfig_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2769_; 
v___x_2725_ = l_Lean_Meta_Context_config(v___y_2719_);
v_foApprox_2726_ = lean_ctor_get_uint8(v___x_2725_, 0);
v_ctxApprox_2727_ = lean_ctor_get_uint8(v___x_2725_, 1);
v_quasiPatternApprox_2728_ = lean_ctor_get_uint8(v___x_2725_, 2);
v_constApprox_2729_ = lean_ctor_get_uint8(v___x_2725_, 3);
v_isDefEqStuckEx_2730_ = lean_ctor_get_uint8(v___x_2725_, 4);
v_unificationHints_2731_ = lean_ctor_get_uint8(v___x_2725_, 5);
v_proofIrrelevance_2732_ = lean_ctor_get_uint8(v___x_2725_, 6);
v_assignSyntheticOpaque_2733_ = lean_ctor_get_uint8(v___x_2725_, 7);
v_offsetCnstrs_2734_ = lean_ctor_get_uint8(v___x_2725_, 8);
v_transparency_2735_ = lean_ctor_get_uint8(v___x_2725_, 9);
v_univApprox_2736_ = lean_ctor_get_uint8(v___x_2725_, 11);
v_zetaUnused_2737_ = lean_ctor_get_uint8(v___x_2725_, 17);
v_canUnfoldPredicateConfig_2738_ = lean_ctor_get_uint8(v___x_2725_, 19);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2740_ = v___x_2725_;
v_isShared_2741_ = v_isSharedCheck_2769_;
goto v_resetjp_2739_;
}
else
{
lean_dec(v___x_2725_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2769_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
uint8_t v___x_2742_; uint8_t v___x_2743_; uint8_t v___x_2744_; lean_object* v___x_2746_; 
v___x_2742_ = 1;
v___x_2743_ = 0;
v___x_2744_ = 2;
if (v_isShared_2741_ == 0)
{
v___x_2746_ = v___x_2740_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 0, v_foApprox_2726_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 1, v_ctxApprox_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 2, v_quasiPatternApprox_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 3, v_constApprox_2729_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 4, v_isDefEqStuckEx_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 5, v_unificationHints_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 6, v_proofIrrelevance_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 7, v_assignSyntheticOpaque_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 8, v_offsetCnstrs_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 9, v_transparency_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 11, v_univApprox_2736_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 17, v_zetaUnused_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 19, v_canUnfoldPredicateConfig_2738_);
v___x_2746_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
uint8_t v_trackZetaDelta_2747_; lean_object* v_zetaDeltaSet_2748_; lean_object* v_lctx_2749_; lean_object* v_localInstances_2750_; lean_object* v_defEqCtx_x3f_2751_; lean_object* v_synthPendingDepth_2752_; lean_object* v_customCanUnfoldPredicate_x3f_2753_; uint8_t v_univApprox_2754_; uint8_t v_inTypeClassResolution_2755_; uint8_t v_cacheInferType_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2766_; 
lean_ctor_set_uint8(v___x_2746_, 10, v___x_2743_);
lean_ctor_set_uint8(v___x_2746_, 12, v___x_2742_);
lean_ctor_set_uint8(v___x_2746_, 13, v___x_2742_);
lean_ctor_set_uint8(v___x_2746_, 14, v___x_2744_);
lean_ctor_set_uint8(v___x_2746_, 15, v___x_2742_);
lean_ctor_set_uint8(v___x_2746_, 16, v___x_2742_);
lean_ctor_set_uint8(v___x_2746_, 18, v___x_2742_);
v_trackZetaDelta_2747_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*7);
v_zetaDeltaSet_2748_ = lean_ctor_get(v___y_2719_, 1);
v_lctx_2749_ = lean_ctor_get(v___y_2719_, 2);
v_localInstances_2750_ = lean_ctor_get(v___y_2719_, 3);
v_defEqCtx_x3f_2751_ = lean_ctor_get(v___y_2719_, 4);
v_synthPendingDepth_2752_ = lean_ctor_get(v___y_2719_, 5);
v_customCanUnfoldPredicate_x3f_2753_ = lean_ctor_get(v___y_2719_, 6);
v_univApprox_2754_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2755_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*7 + 2);
v_cacheInferType_2756_ = lean_ctor_get_uint8(v___y_2719_, sizeof(void*)*7 + 3);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___y_2719_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v___y_2719_, 0);
lean_dec(v_unused_2767_);
v___x_2758_ = v___y_2719_;
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2753_);
lean_inc(v_synthPendingDepth_2752_);
lean_inc(v_defEqCtx_x3f_2751_);
lean_inc(v_localInstances_2750_);
lean_inc(v_lctx_2749_);
lean_inc(v_zetaDeltaSet_2748_);
lean_dec(v___y_2719_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
uint64_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2760_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2746_);
v___x_2761_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2761_, 0, v___x_2746_);
lean_ctor_set_uint64(v___x_2761_, sizeof(void*)*1, v___x_2760_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2761_);
v___x_2763_ = v___x_2758_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_zetaDeltaSet_2748_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_lctx_2749_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v_localInstances_2750_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v_defEqCtx_x3f_2751_);
lean_ctor_set(v_reuseFailAlloc_2765_, 5, v_synthPendingDepth_2752_);
lean_ctor_set(v_reuseFailAlloc_2765_, 6, v_customCanUnfoldPredicate_x3f_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*7, v_trackZetaDelta_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*7 + 1, v_univApprox_2754_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2755_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*7 + 3, v_cacheInferType_2756_);
v___x_2763_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_apply_5(v_x_2718_, v___x_2763_, v___y_2720_, v___y_2721_, v___y_2722_, lean_box(0));
return v___x_2764_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withInferTypeConfig___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2718_ = stack[0].m_obj;
lean_object* v___y_2719_ = stack[1].m_obj;
lean_object* v___y_2720_ = stack[2].m_obj;
lean_object* v___y_2721_ = stack[3].m_obj;
lean_object* v___y_2722_ = stack[4].m_obj;
lean_object* v_res_2785_;
v_res_2785_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
stack->m_obj
 = v_res_2785_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v_res_2792_;
}
}
lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___y_2800_; lean_object* v___x_2817_; uint8_t v_transparency_2818_; uint8_t v___x_2819_; uint8_t v___x_2820_; 
v___x_2817_ = l_Lean_Meta_Context_config(v_a_2794_);
v_transparency_2818_ = lean_ctor_get_uint8(v___x_2817_, 9);
lean_dec_ref(v___x_2817_);
v___x_2819_ = 1;
v___x_2820_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2818_, v___x_2819_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; 
lean_inc(v_a_2797_);
lean_inc_ref(v_a_2796_);
lean_inc(v_a_2795_);
lean_inc_ref(v_a_2794_);
v___x_2821_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
v___y_2800_ = v___x_2821_;
goto v___jp_2799_;
}
else
{
lean_object* v_keyedConfig_2822_; uint8_t v_trackZetaDelta_2823_; lean_object* v_zetaDeltaSet_2824_; lean_object* v_lctx_2825_; lean_object* v_localInstances_2826_; lean_object* v_defEqCtx_x3f_2827_; lean_object* v_synthPendingDepth_2828_; lean_object* v_customCanUnfoldPredicate_x3f_2829_; uint8_t v_univApprox_2830_; uint8_t v_inTypeClassResolution_2831_; uint8_t v_cacheInferType_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_keyedConfig_2822_ = lean_ctor_get(v_a_2794_, 0);
v_trackZetaDelta_2823_ = lean_ctor_get_uint8(v_a_2794_, sizeof(void*)*7);
v_zetaDeltaSet_2824_ = lean_ctor_get(v_a_2794_, 1);
v_lctx_2825_ = lean_ctor_get(v_a_2794_, 2);
v_localInstances_2826_ = lean_ctor_get(v_a_2794_, 3);
v_defEqCtx_x3f_2827_ = lean_ctor_get(v_a_2794_, 4);
v_synthPendingDepth_2828_ = lean_ctor_get(v_a_2794_, 5);
v_customCanUnfoldPredicate_x3f_2829_ = lean_ctor_get(v_a_2794_, 6);
v_univApprox_2830_ = lean_ctor_get_uint8(v_a_2794_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2831_ = lean_ctor_get_uint8(v_a_2794_, sizeof(void*)*7 + 2);
v_cacheInferType_2832_ = lean_ctor_get_uint8(v_a_2794_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2822_);
v___x_2833_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2819_, v_keyedConfig_2822_);
lean_inc(v_customCanUnfoldPredicate_x3f_2829_);
lean_inc(v_synthPendingDepth_2828_);
lean_inc(v_defEqCtx_x3f_2827_);
lean_inc_ref(v_localInstances_2826_);
lean_inc_ref(v_lctx_2825_);
lean_inc(v_zetaDeltaSet_2824_);
v___x_2834_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
lean_ctor_set(v___x_2834_, 1, v_zetaDeltaSet_2824_);
lean_ctor_set(v___x_2834_, 2, v_lctx_2825_);
lean_ctor_set(v___x_2834_, 3, v_localInstances_2826_);
lean_ctor_set(v___x_2834_, 4, v_defEqCtx_x3f_2827_);
lean_ctor_set(v___x_2834_, 5, v_synthPendingDepth_2828_);
lean_ctor_set(v___x_2834_, 6, v_customCanUnfoldPredicate_x3f_2829_);
lean_ctor_set_uint8(v___x_2834_, sizeof(void*)*7, v_trackZetaDelta_2823_);
lean_ctor_set_uint8(v___x_2834_, sizeof(void*)*7 + 1, v_univApprox_2830_);
lean_ctor_set_uint8(v___x_2834_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2831_);
lean_ctor_set_uint8(v___x_2834_, sizeof(void*)*7 + 3, v_cacheInferType_2832_);
lean_inc(v_a_2797_);
lean_inc_ref(v_a_2796_);
lean_inc(v_a_2795_);
v___x_2835_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2793_, v___x_2834_, v_a_2795_, v_a_2796_, v_a_2797_);
v___y_2800_ = v___x_2835_;
goto v___jp_2799_;
}
v___jp_2799_:
{
if (lean_obj_tag(v___y_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_a_2801_ = lean_ctor_get(v___y_2800_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___y_2800_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___y_2800_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___y_2800_);
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
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v___y_2800_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___y_2800_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___y_2800_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___y_2800_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withInferTypeConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2793_ = stack[0].m_obj;
lean_object* v_a_2794_ = stack[1].m_obj;
lean_object* v_a_2795_ = stack[2].m_obj;
lean_object* v_a_2796_ = stack[3].m_obj;
lean_object* v_a_2797_ = stack[4].m_obj;
lean_object* v_res_2836_;
v_res_2836_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
stack->m_obj
 = v_res_2836_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
return v_res_2843_;
}
}
lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2844_, lean_object* v_x_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___y_2852_; lean_object* v___x_2869_; uint8_t v_transparency_2870_; uint8_t v___x_2871_; uint8_t v___x_2872_; 
v___x_2869_ = l_Lean_Meta_Context_config(v_a_2846_);
v_transparency_2870_ = lean_ctor_get_uint8(v___x_2869_, 9);
lean_dec_ref(v___x_2869_);
v___x_2871_ = 1;
v___x_2872_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2870_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_inc(v_a_2849_);
lean_inc_ref(v_a_2848_);
lean_inc(v_a_2847_);
lean_inc_ref(v_a_2846_);
v___x_2873_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
v___y_2852_ = v___x_2873_;
goto v___jp_2851_;
}
else
{
lean_object* v_keyedConfig_2874_; uint8_t v_trackZetaDelta_2875_; lean_object* v_zetaDeltaSet_2876_; lean_object* v_lctx_2877_; lean_object* v_localInstances_2878_; lean_object* v_defEqCtx_x3f_2879_; lean_object* v_synthPendingDepth_2880_; lean_object* v_customCanUnfoldPredicate_x3f_2881_; uint8_t v_univApprox_2882_; uint8_t v_inTypeClassResolution_2883_; uint8_t v_cacheInferType_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_keyedConfig_2874_ = lean_ctor_get(v_a_2846_, 0);
v_trackZetaDelta_2875_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7);
v_zetaDeltaSet_2876_ = lean_ctor_get(v_a_2846_, 1);
v_lctx_2877_ = lean_ctor_get(v_a_2846_, 2);
v_localInstances_2878_ = lean_ctor_get(v_a_2846_, 3);
v_defEqCtx_x3f_2879_ = lean_ctor_get(v_a_2846_, 4);
v_synthPendingDepth_2880_ = lean_ctor_get(v_a_2846_, 5);
v_customCanUnfoldPredicate_x3f_2881_ = lean_ctor_get(v_a_2846_, 6);
v_univApprox_2882_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2883_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7 + 2);
v_cacheInferType_2884_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2874_);
v___x_2885_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2871_, v_keyedConfig_2874_);
lean_inc(v_customCanUnfoldPredicate_x3f_2881_);
lean_inc(v_synthPendingDepth_2880_);
lean_inc(v_defEqCtx_x3f_2879_);
lean_inc_ref(v_localInstances_2878_);
lean_inc_ref(v_lctx_2877_);
lean_inc(v_zetaDeltaSet_2876_);
v___x_2886_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v_zetaDeltaSet_2876_);
lean_ctor_set(v___x_2886_, 2, v_lctx_2877_);
lean_ctor_set(v___x_2886_, 3, v_localInstances_2878_);
lean_ctor_set(v___x_2886_, 4, v_defEqCtx_x3f_2879_);
lean_ctor_set(v___x_2886_, 5, v_synthPendingDepth_2880_);
lean_ctor_set(v___x_2886_, 6, v_customCanUnfoldPredicate_x3f_2881_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7, v_trackZetaDelta_2875_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 1, v_univApprox_2882_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2883_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*7 + 3, v_cacheInferType_2884_);
lean_inc(v_a_2849_);
lean_inc_ref(v_a_2848_);
lean_inc(v_a_2847_);
v___x_2887_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2845_, v___x_2886_, v_a_2847_, v_a_2848_, v_a_2849_);
v___y_2852_ = v___x_2887_;
goto v___jp_2851_;
}
v___jp_2851_:
{
if (lean_obj_tag(v___y_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
v_a_2853_ = lean_ctor_get(v___y_2852_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___y_2852_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___y_2852_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___y_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
v_a_2861_ = lean_ctor_get(v___y_2852_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___y_2852_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___y_2852_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___y_2852_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withInferTypeConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2845_ = stack[1].m_obj;
lean_object* v_a_2846_ = stack[2].m_obj;
lean_object* v_a_2847_ = stack[3].m_obj;
lean_object* v_a_2848_ = stack[4].m_obj;
lean_object* v_a_2849_ = stack[5].m_obj;
lean_object* v_res_2888_;
v_res_2888_ = l_Lean_Meta_withInferTypeConfig(lean_box(0), v_x_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
stack->m_obj
 = v_res_2888_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2889_, lean_object* v_x_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2889_, v_x_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
return v_res_2896_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_box(0);
v___x_2898_ = l_Lean_interruptExceptionId;
v___x_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v___x_2897_);
return v___x_2899_;
}
}
lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2903_;
v_res_2903_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
stack->m_obj
 = v_res_2903_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2905_;
}
}
lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2910_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2907_ = stack[1].m_obj;
lean_object* v___y_2908_ = stack[2].m_obj;
lean_object* v_res_2911_;
v_res_2911_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_box(0), v___y_2907_, v___y_2908_);
stack->m_obj
 = v_res_2911_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_){
_start:
{
lean_object* v_ks_2921_; lean_object* v_vs_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2951_; 
v_ks_2921_ = lean_ctor_get(v_x_2917_, 0);
v_vs_2922_ = lean_ctor_get(v_x_2917_, 1);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_x_2917_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2924_ = v_x_2917_;
v_isShared_2925_ = v_isSharedCheck_2951_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_vs_2922_);
lean_inc(v_ks_2921_);
lean_dec(v_x_2917_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2951_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
uint8_t v___y_2927_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = lean_array_get_size(v_ks_2921_);
v___x_2940_ = lean_nat_dec_lt(v_x_2918_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_del_object(v___x_2924_);
lean_dec(v_x_2918_);
v___x_2941_ = lean_array_push(v_ks_2921_, v_x_2919_);
v___x_2942_ = lean_array_push(v_vs_2922_, v_x_2920_);
v___x_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
return v___x_2943_;
}
else
{
lean_object* v_expr_2944_; uint64_t v_configKey_2945_; lean_object* v_k_x27_2946_; lean_object* v_expr_2947_; uint64_t v_configKey_2948_; uint8_t v___x_2949_; 
v_expr_2944_ = lean_ctor_get(v_x_2919_, 0);
v_configKey_2945_ = lean_ctor_get_uint64(v_x_2919_, sizeof(void*)*1);
v_k_x27_2946_ = lean_array_fget_borrowed(v_ks_2921_, v_x_2918_);
v_expr_2947_ = lean_ctor_get(v_k_x27_2946_, 0);
v_configKey_2948_ = lean_ctor_get_uint64(v_k_x27_2946_, sizeof(void*)*1);
v___x_2949_ = lean_expr_equal(v_expr_2944_, v_expr_2947_);
if (v___x_2949_ == 0)
{
v___y_2927_ = v___x_2949_;
goto v___jp_2926_;
}
else
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_uint64_dec_eq(v_configKey_2945_, v_configKey_2948_);
v___y_2927_ = v___x_2950_;
goto v___jp_2926_;
}
}
v___jp_2926_:
{
if (v___y_2927_ == 0)
{
lean_object* v___x_2929_; 
if (v_isShared_2925_ == 0)
{
v___x_2929_ = v___x_2924_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_ks_2921_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_vs_2922_);
v___x_2929_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_unsigned_to_nat(1u);
v___x_2931_ = lean_nat_add(v_x_2918_, v___x_2930_);
lean_dec(v_x_2918_);
v_x_2917_ = v___x_2929_;
v_x_2918_ = v___x_2931_;
goto _start;
}
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2934_ = lean_array_fset(v_ks_2921_, v_x_2918_, v_x_2919_);
v___x_2935_ = lean_array_fset(v_vs_2922_, v_x_2918_, v_x_2920_);
lean_dec(v_x_2918_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v___x_2935_);
lean_ctor_set(v___x_2924_, 0, v___x_2934_);
v___x_2937_ = v___x_2924_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2952_, lean_object* v_k_2953_, lean_object* v_v_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2952_, v___x_2955_, v_k_2953_, v_v_2954_);
return v___x_2956_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2957_, size_t v_x_2958_, size_t v_x_2959_, lean_object* v_x_2960_, lean_object* v_x_2961_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 0)
{
lean_object* v_es_2962_; size_t v___x_2963_; size_t v___x_2964_; lean_object* v_j_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v_es_2962_ = lean_ctor_get(v_x_2957_, 0);
v___x_2963_ = ((size_t)31ULL);
v___x_2964_ = lean_usize_land(v_x_2958_, v___x_2963_);
v_j_2965_ = lean_usize_to_nat(v___x_2964_);
v___x_2966_ = lean_array_get_size(v_es_2962_);
v___x_2967_ = lean_nat_dec_lt(v_j_2965_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_dec(v_j_2965_);
lean_dec(v_x_2961_);
lean_dec_ref(v_x_2960_);
return v_x_2957_;
}
else
{
lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3013_; 
lean_inc_ref(v_es_2962_);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_x_2957_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v_x_2957_, 0);
lean_dec(v_unused_3014_);
v___x_2969_ = v_x_2957_;
v_isShared_2970_ = v_isSharedCheck_3013_;
goto v_resetjp_2968_;
}
else
{
lean_dec(v_x_2957_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3013_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_v_2971_; lean_object* v___x_2972_; lean_object* v_xs_x27_2973_; lean_object* v___y_2975_; 
v_v_2971_ = lean_array_fget(v_es_2962_, v_j_2965_);
v___x_2972_ = lean_box(0);
v_xs_x27_2973_ = lean_array_fset(v_es_2962_, v_j_2965_, v___x_2972_);
switch(lean_obj_tag(v_v_2971_))
{
case 0:
{
lean_object* v_key_2980_; lean_object* v_val_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2998_; 
v_key_2980_ = lean_ctor_get(v_v_2971_, 0);
v_val_2981_ = lean_ctor_get(v_v_2971_, 1);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_v_2971_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2983_ = v_v_2971_;
v_isShared_2984_ = v_isSharedCheck_2998_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_val_2981_);
lean_inc(v_key_2980_);
lean_dec(v_v_2971_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2998_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
uint8_t v___y_2986_; lean_object* v_expr_2992_; uint64_t v_configKey_2993_; lean_object* v_expr_2994_; uint64_t v_configKey_2995_; uint8_t v___x_2996_; 
v_expr_2992_ = lean_ctor_get(v_x_2960_, 0);
v_configKey_2993_ = lean_ctor_get_uint64(v_x_2960_, sizeof(void*)*1);
v_expr_2994_ = lean_ctor_get(v_key_2980_, 0);
v_configKey_2995_ = lean_ctor_get_uint64(v_key_2980_, sizeof(void*)*1);
v___x_2996_ = lean_expr_equal(v_expr_2992_, v_expr_2994_);
if (v___x_2996_ == 0)
{
v___y_2986_ = v___x_2996_;
goto v___jp_2985_;
}
else
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_uint64_dec_eq(v_configKey_2993_, v_configKey_2995_);
v___y_2986_ = v___x_2997_;
goto v___jp_2985_;
}
v___jp_2985_:
{
if (v___y_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_del_object(v___x_2983_);
v___x_2987_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2980_, v_val_2981_, v_x_2960_, v_x_2961_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
v___y_2975_ = v___x_2988_;
goto v___jp_2974_;
}
else
{
lean_object* v___x_2990_; 
lean_dec(v_val_2981_);
lean_dec(v_key_2980_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v_x_2961_);
lean_ctor_set(v___x_2983_, 0, v_x_2960_);
v___x_2990_ = v___x_2983_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_x_2960_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_x_2961_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
v___y_2975_ = v___x_2990_;
goto v___jp_2974_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3011_; 
v_node_2999_ = lean_ctor_get(v_v_2971_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_v_2971_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3001_ = v_v_2971_;
v_isShared_3002_ = v_isSharedCheck_3011_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_node_2999_);
lean_dec(v_v_2971_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3011_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
size_t v___x_3003_; size_t v___x_3004_; size_t v___x_3005_; size_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3003_ = ((size_t)5ULL);
v___x_3004_ = lean_usize_shift_right(v_x_2958_, v___x_3003_);
v___x_3005_ = ((size_t)1ULL);
v___x_3006_ = lean_usize_add(v_x_2959_, v___x_3005_);
v___x_3007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2999_, v___x_3004_, v___x_3006_, v_x_2960_, v_x_2961_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3007_);
v___x_3009_ = v___x_3001_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v___y_2975_ = v___x_3009_;
goto v___jp_2974_;
}
}
}
default: 
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v_x_2960_);
lean_ctor_set(v___x_3012_, 1, v_x_2961_);
v___y_2975_ = v___x_3012_;
goto v___jp_2974_;
}
}
v___jp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_array_fset(v_xs_x27_2973_, v_j_2965_, v___y_2975_);
lean_dec(v_j_2965_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 0, v___x_2976_);
v___x_2978_ = v___x_2969_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
else
{
lean_object* v_ks_3015_; lean_object* v_vs_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3034_; 
v_ks_3015_ = lean_ctor_get(v_x_2957_, 0);
v_vs_3016_ = lean_ctor_get(v_x_2957_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_x_2957_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3018_ = v_x_2957_;
v_isShared_3019_ = v_isSharedCheck_3034_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_vs_3016_);
lean_inc(v_ks_3015_);
lean_dec(v_x_2957_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3034_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_ks_3015_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v_vs_3016_);
v___x_3021_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v_newNode_3022_; size_t v___x_3023_; uint8_t v___x_3024_; 
v_newNode_3022_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_3021_, v_x_2960_, v_x_2961_);
v___x_3023_ = ((size_t)7ULL);
v___x_3024_ = lean_usize_dec_le(v___x_3023_, v_x_2959_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3025_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3022_);
v___x_3026_ = lean_unsigned_to_nat(4u);
v___x_3027_ = lean_nat_dec_lt(v___x_3025_, v___x_3026_);
lean_dec(v___x_3025_);
if (v___x_3027_ == 0)
{
lean_object* v_ks_3028_; lean_object* v_vs_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_ks_3028_ = lean_ctor_get(v_newNode_3022_, 0);
lean_inc_ref(v_ks_3028_);
v_vs_3029_ = lean_ctor_get(v_newNode_3022_, 1);
lean_inc_ref(v_vs_3029_);
lean_dec_ref(v_newNode_3022_);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3032_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2959_, v_ks_3028_, v_vs_3029_, v___x_3030_, v___x_3031_);
lean_dec_ref(v_vs_3029_);
lean_dec_ref(v_ks_3028_);
return v___x_3032_;
}
else
{
return v_newNode_3022_;
}
}
else
{
return v_newNode_3022_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2957_ = stack[0].m_obj;
size_t v_x_2958_ = stack[1].m_num;
size_t v_x_2959_ = stack[2].m_num;
lean_object* v_x_2960_ = stack[3].m_obj;
lean_object* v_x_2961_ = stack[4].m_obj;
lean_object* v_res_3035_;
v_res_3035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2957_, v_x_2958_, v_x_2959_, v_x_2960_, v_x_2961_);
stack->m_obj
 = v_res_3035_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3036_, lean_object* v_keys_3037_, lean_object* v_vals_3038_, lean_object* v_i_3039_, lean_object* v_entries_3040_){
_start:
{
lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = lean_array_get_size(v_keys_3037_);
v___x_3042_ = lean_nat_dec_lt(v_i_3039_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_dec(v_i_3039_);
return v_entries_3040_;
}
else
{
lean_object* v_k_3043_; lean_object* v_expr_3044_; uint64_t v_configKey_3045_; lean_object* v_v_3046_; uint64_t v___x_3047_; uint64_t v___x_3048_; size_t v_h_3049_; size_t v___x_3050_; lean_object* v___x_3051_; size_t v___x_3052_; size_t v___x_3053_; size_t v___x_3054_; size_t v_h_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v_k_3043_ = lean_array_fget_borrowed(v_keys_3037_, v_i_3039_);
v_expr_3044_ = lean_ctor_get(v_k_3043_, 0);
v_configKey_3045_ = lean_ctor_get_uint64(v_k_3043_, sizeof(void*)*1);
v_v_3046_ = lean_array_fget_borrowed(v_vals_3038_, v_i_3039_);
v___x_3047_ = l_Lean_Expr_hash(v_expr_3044_);
v___x_3048_ = lean_uint64_mix_hash(v___x_3047_, v_configKey_3045_);
v_h_3049_ = lean_uint64_to_usize(v___x_3048_);
v___x_3050_ = ((size_t)5ULL);
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = ((size_t)1ULL);
v___x_3053_ = lean_usize_sub(v_depth_3036_, v___x_3052_);
v___x_3054_ = lean_usize_mul(v___x_3050_, v___x_3053_);
v_h_3055_ = lean_usize_shift_right(v_h_3049_, v___x_3054_);
v___x_3056_ = lean_nat_add(v_i_3039_, v___x_3051_);
lean_dec(v_i_3039_);
lean_inc(v_v_3046_);
lean_inc(v_k_3043_);
v___x_3057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3040_, v_h_3055_, v_depth_3036_, v_k_3043_, v_v_3046_);
v_i_3039_ = v___x_3056_;
v_entries_3040_ = v___x_3057_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3036_ = stack[0].m_num;
lean_object* v_keys_3037_ = stack[1].m_obj;
lean_object* v_vals_3038_ = stack[2].m_obj;
lean_object* v_i_3039_ = stack[3].m_obj;
lean_object* v_entries_3040_ = stack[4].m_obj;
lean_object* v_res_3059_;
v_res_3059_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3036_, v_keys_3037_, v_vals_3038_, v_i_3039_, v_entries_3040_);
stack->m_obj
 = v_res_3059_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3060_, lean_object* v_keys_3061_, lean_object* v_vals_3062_, lean_object* v_i_3063_, lean_object* v_entries_3064_){
_start:
{
size_t v_depth_boxed_3065_; lean_object* v_res_3066_; 
v_depth_boxed_3065_ = lean_unbox_usize(v_depth_3060_);
lean_dec(v_depth_3060_);
v_res_3066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3065_, v_keys_3061_, v_vals_3062_, v_i_3063_, v_entries_3064_);
lean_dec_ref(v_vals_3062_);
lean_dec_ref(v_keys_3061_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3067_, lean_object* v_x_3068_, lean_object* v_x_3069_, lean_object* v_x_3070_, lean_object* v_x_3071_){
_start:
{
size_t v_x_2441__boxed_3072_; size_t v_x_2442__boxed_3073_; lean_object* v_res_3074_; 
v_x_2441__boxed_3072_ = lean_unbox_usize(v_x_3068_);
lean_dec(v_x_3068_);
v_x_2442__boxed_3073_ = lean_unbox_usize(v_x_3069_);
lean_dec(v_x_3069_);
v_res_3074_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3067_, v_x_2441__boxed_3072_, v_x_2442__boxed_3073_, v_x_3070_, v_x_3071_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3075_, lean_object* v_x_3076_, lean_object* v_x_3077_){
_start:
{
lean_object* v_expr_3078_; uint64_t v_configKey_3079_; uint64_t v___x_3080_; uint64_t v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; lean_object* v___x_3084_; 
v_expr_3078_ = lean_ctor_get(v_x_3076_, 0);
v_configKey_3079_ = lean_ctor_get_uint64(v_x_3076_, sizeof(void*)*1);
v___x_3080_ = l_Lean_Expr_hash(v_expr_3078_);
v___x_3081_ = lean_uint64_mix_hash(v___x_3080_, v_configKey_3079_);
v___x_3082_ = lean_uint64_to_usize(v___x_3081_);
v___x_3083_ = ((size_t)1ULL);
v___x_3084_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3075_, v___x_3082_, v___x_3083_, v_x_3076_, v_x_3077_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3085_, lean_object* v_vals_3086_, lean_object* v_i_3087_, lean_object* v_k_3088_){
_start:
{
uint8_t v___y_3090_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = lean_array_get_size(v_keys_3085_);
v___x_3097_ = lean_nat_dec_lt(v_i_3087_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; 
lean_dec(v_i_3087_);
v___x_3098_ = lean_box(0);
return v___x_3098_;
}
else
{
lean_object* v_expr_3099_; uint64_t v_configKey_3100_; lean_object* v_k_x27_3101_; lean_object* v_expr_3102_; uint64_t v_configKey_3103_; uint8_t v___x_3104_; 
v_expr_3099_ = lean_ctor_get(v_k_3088_, 0);
v_configKey_3100_ = lean_ctor_get_uint64(v_k_3088_, sizeof(void*)*1);
v_k_x27_3101_ = lean_array_fget_borrowed(v_keys_3085_, v_i_3087_);
v_expr_3102_ = lean_ctor_get(v_k_x27_3101_, 0);
v_configKey_3103_ = lean_ctor_get_uint64(v_k_x27_3101_, sizeof(void*)*1);
v___x_3104_ = lean_expr_equal(v_expr_3099_, v_expr_3102_);
if (v___x_3104_ == 0)
{
v___y_3090_ = v___x_3104_;
goto v___jp_3089_;
}
else
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_uint64_dec_eq(v_configKey_3100_, v_configKey_3103_);
v___y_3090_ = v___x_3105_;
goto v___jp_3089_;
}
}
v___jp_3089_:
{
if (v___y_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_unsigned_to_nat(1u);
v___x_3092_ = lean_nat_add(v_i_3087_, v___x_3091_);
lean_dec(v_i_3087_);
v_i_3087_ = v___x_3092_;
goto _start;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_array_fget_borrowed(v_vals_3086_, v_i_3087_);
lean_dec(v_i_3087_);
lean_inc(v___x_3094_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
return v___x_3095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3106_, lean_object* v_vals_3107_, lean_object* v_i_3108_, lean_object* v_k_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3106_, v_vals_3107_, v_i_3108_, v_k_3109_);
lean_dec_ref(v_k_3109_);
lean_dec_ref(v_vals_3107_);
lean_dec_ref(v_keys_3106_);
return v_res_3110_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3111_, size_t v_x_3112_, lean_object* v_x_3113_){
_start:
{
if (lean_obj_tag(v_x_3111_) == 0)
{
lean_object* v_es_3114_; lean_object* v___x_3115_; size_t v___x_3116_; size_t v___x_3117_; lean_object* v_j_3118_; lean_object* v___x_3119_; 
v_es_3114_ = lean_ctor_get(v_x_3111_, 0);
v___x_3115_ = lean_box(2);
v___x_3116_ = ((size_t)31ULL);
v___x_3117_ = lean_usize_land(v_x_3112_, v___x_3116_);
v_j_3118_ = lean_usize_to_nat(v___x_3117_);
v___x_3119_ = lean_array_get_borrowed(v___x_3115_, v_es_3114_, v_j_3118_);
lean_dec(v_j_3118_);
switch(lean_obj_tag(v___x_3119_))
{
case 0:
{
lean_object* v_key_3120_; lean_object* v_val_3121_; uint8_t v___y_3123_; lean_object* v_expr_3126_; uint64_t v_configKey_3127_; lean_object* v_expr_3128_; uint64_t v_configKey_3129_; uint8_t v___x_3130_; 
v_key_3120_ = lean_ctor_get(v___x_3119_, 0);
v_val_3121_ = lean_ctor_get(v___x_3119_, 1);
v_expr_3126_ = lean_ctor_get(v_x_3113_, 0);
v_configKey_3127_ = lean_ctor_get_uint64(v_x_3113_, sizeof(void*)*1);
v_expr_3128_ = lean_ctor_get(v_key_3120_, 0);
v_configKey_3129_ = lean_ctor_get_uint64(v_key_3120_, sizeof(void*)*1);
v___x_3130_ = lean_expr_equal(v_expr_3126_, v_expr_3128_);
if (v___x_3130_ == 0)
{
v___y_3123_ = v___x_3130_;
goto v___jp_3122_;
}
else
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_uint64_dec_eq(v_configKey_3127_, v_configKey_3129_);
v___y_3123_ = v___x_3131_;
goto v___jp_3122_;
}
v___jp_3122_:
{
if (v___y_3123_ == 0)
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_box(0);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; 
lean_inc(v_val_3121_);
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_val_3121_);
return v___x_3125_;
}
}
}
case 1:
{
lean_object* v_node_3132_; size_t v___x_3133_; size_t v___x_3134_; 
v_node_3132_ = lean_ctor_get(v___x_3119_, 0);
v___x_3133_ = ((size_t)5ULL);
v___x_3134_ = lean_usize_shift_right(v_x_3112_, v___x_3133_);
v_x_3111_ = v_node_3132_;
v_x_3112_ = v___x_3134_;
goto _start;
}
default: 
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_box(0);
return v___x_3136_;
}
}
}
else
{
lean_object* v_ks_3137_; lean_object* v_vs_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_ks_3137_ = lean_ctor_get(v_x_3111_, 0);
v_vs_3138_ = lean_ctor_get(v_x_3111_, 1);
v___x_3139_ = lean_unsigned_to_nat(0u);
v___x_3140_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3137_, v_vs_3138_, v___x_3139_, v_x_3113_);
return v___x_3140_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3111_ = stack[0].m_obj;
size_t v_x_3112_ = stack[1].m_num;
lean_object* v_x_3113_ = stack[2].m_obj;
lean_object* v_res_3141_;
v_res_3141_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3111_, v_x_3112_, v_x_3113_);
stack->m_obj
 = v_res_3141_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3142_, lean_object* v_x_3143_, lean_object* v_x_3144_){
_start:
{
size_t v_x_2756__boxed_3145_; lean_object* v_res_3146_; 
v_x_2756__boxed_3145_ = lean_unbox_usize(v_x_3143_);
lean_dec(v_x_3143_);
v_res_3146_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3142_, v_x_2756__boxed_3145_, v_x_3144_);
lean_dec_ref(v_x_3144_);
lean_dec_ref(v_x_3142_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3147_, lean_object* v_x_3148_){
_start:
{
lean_object* v_expr_3149_; uint64_t v_configKey_3150_; uint64_t v___x_3151_; uint64_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v_expr_3149_ = lean_ctor_get(v_x_3148_, 0);
v_configKey_3150_ = lean_ctor_get_uint64(v_x_3148_, sizeof(void*)*1);
v___x_3151_ = l_Lean_Expr_hash(v_expr_3149_);
v___x_3152_ = lean_uint64_mix_hash(v___x_3151_, v_configKey_3150_);
v___x_3153_ = lean_uint64_to_usize(v___x_3152_);
v___x_3154_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3147_, v___x_3153_, v_x_3148_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3155_, lean_object* v_x_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3155_, v_x_3156_);
lean_dec_ref(v_x_3156_);
lean_dec_ref(v_x_3155_);
return v_res_3157_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3160_ = l_Lean_stringToMessageData(v___x_3159_);
return v___x_3160_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
switch(lean_obj_tag(v_e_3161_))
{
case 0:
{
lean_object* v_deBruijnIndex_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_deBruijnIndex_3199_ = lean_ctor_get(v_e_3161_, 0);
lean_inc(v_deBruijnIndex_3199_);
lean_dec_ref_known(v_e_3161_, 1);
v___x_3200_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3201_ = l_Lean_mkBVar(v_deBruijnIndex_3199_);
v___x_3202_ = l_Lean_MessageData_ofExpr(v___x_3201_);
v___x_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3200_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3203_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3204_;
}
case 1:
{
lean_object* v_fvarId_3205_; lean_object* v___x_3206_; 
v_fvarId_3205_ = lean_ctor_get(v_e_3161_, 0);
lean_inc(v_fvarId_3205_);
lean_dec_ref_known(v_e_3161_, 1);
v___x_3206_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3205_, v_a_3162_, v_a_3164_, v_a_3165_);
return v___x_3206_;
}
case 2:
{
lean_object* v_mvarId_3207_; lean_object* v___x_3208_; 
v_mvarId_3207_ = lean_ctor_get(v_e_3161_, 0);
lean_inc(v_mvarId_3207_);
lean_dec_ref_known(v_e_3161_, 1);
v___x_3208_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3207_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3208_;
}
case 3:
{
lean_object* v_u_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_u_3209_ = lean_ctor_get(v_e_3161_, 0);
lean_inc(v_u_3209_);
lean_dec_ref_known(v_e_3161_, 1);
v___x_3210_ = l_Lean_Level_succ___override(v_u_3209_);
v___x_3211_ = l_Lean_mkSort(v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
case 4:
{
lean_object* v_declName_3213_; lean_object* v_us_3214_; 
v_declName_3213_ = lean_ctor_get(v_e_3161_, 0);
lean_inc(v_declName_3213_);
v_us_3214_ = lean_ctor_get(v_e_3161_, 1);
lean_inc(v_us_3214_);
if (lean_obj_tag(v_us_3214_) == 0)
{
lean_object* v___x_3231_; 
lean_dec_ref_known(v_e_3161_, 2);
v___x_3231_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3213_, v_us_3214_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3231_;
}
else
{
uint8_t v_cacheInferType_3232_; 
v_cacheInferType_3232_ = lean_ctor_get_uint8(v_a_3162_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3232_ == 0)
{
lean_dec_ref_known(v_e_3161_, 2);
goto v___jp_3215_;
}
else
{
uint8_t v___x_3233_; 
v___x_3233_ = l_Lean_Expr_hasMVar(v_e_3161_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3161_, v_a_3162_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3300_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3300_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3300_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3279_; lean_object* v_cache_3280_; lean_object* v_inferType_3281_; lean_object* v___x_3282_; 
v___x_3279_ = lean_st_ref_get(v_a_3163_);
v_cache_3280_ = lean_ctor_get(v___x_3279_, 1);
lean_inc_ref(v_cache_3280_);
lean_dec(v___x_3279_);
v_inferType_3281_ = lean_ctor_get(v_cache_3280_, 0);
lean_inc_ref(v_inferType_3281_);
lean_dec_ref(v_cache_3280_);
v___x_3282_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3281_, v_a_3235_);
lean_dec_ref(v_inferType_3281_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_toCold_3283_; lean_object* v_cancelTk_x3f_3284_; 
lean_del_object(v___x_3237_);
v_toCold_3283_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3284_ = lean_ctor_get(v_toCold_3283_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3284_) == 1)
{
lean_object* v_val_3285_; uint8_t v___x_3286_; 
v_val_3285_ = lean_ctor_get(v_cancelTk_x3f_3284_, 0);
v___x_3286_ = l_IO_CancelToken_isSet(v_val_3285_);
if (v___x_3286_ == 0)
{
goto v___jp_3239_;
}
else
{
lean_object* v___x_3287_; lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec(v_a_3235_);
lean_dec(v_us_3214_);
lean_dec(v_declName_3213_);
v___x_3287_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
goto v___jp_3239_;
}
}
else
{
lean_object* v_val_3296_; lean_object* v___x_3298_; 
lean_dec(v_a_3235_);
lean_dec(v_us_3214_);
lean_dec(v_declName_3213_);
v_val_3296_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_val_3296_);
lean_dec_ref_known(v___x_3282_, 1);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v_val_3296_);
v___x_3298_ = v___x_3237_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_val_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
v___jp_3239_:
{
lean_object* v___x_3240_; 
v___x_3240_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3213_, v_us_3214_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; uint8_t v___x_3242_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v___x_3242_ = l_Lean_Expr_hasMVar(v_a_3241_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3277_; 
lean_inc(v_a_3241_);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v___x_3240_, 0);
lean_dec(v_unused_3278_);
v___x_3244_ = v___x_3240_;
v_isShared_3245_ = v_isSharedCheck_3277_;
goto v_resetjp_3243_;
}
else
{
lean_dec(v___x_3240_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3277_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v_cache_3247_; lean_object* v_mctx_3248_; lean_object* v_zetaDeltaFVarIds_3249_; lean_object* v_postponed_3250_; lean_object* v_diag_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3276_; 
v___x_3246_ = lean_st_ref_take(v_a_3163_);
v_cache_3247_ = lean_ctor_get(v___x_3246_, 1);
v_mctx_3248_ = lean_ctor_get(v___x_3246_, 0);
v_zetaDeltaFVarIds_3249_ = lean_ctor_get(v___x_3246_, 2);
v_postponed_3250_ = lean_ctor_get(v___x_3246_, 3);
v_diag_3251_ = lean_ctor_get(v___x_3246_, 4);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3253_ = v___x_3246_;
v_isShared_3254_ = v_isSharedCheck_3276_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_diag_3251_);
lean_inc(v_postponed_3250_);
lean_inc(v_zetaDeltaFVarIds_3249_);
lean_inc(v_cache_3247_);
lean_inc(v_mctx_3248_);
lean_dec(v___x_3246_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3276_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v_inferType_3255_; lean_object* v_funInfo_3256_; lean_object* v_synthInstance_3257_; lean_object* v_whnf_3258_; lean_object* v_defEqTrans_3259_; lean_object* v_defEqPerm_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3275_; 
v_inferType_3255_ = lean_ctor_get(v_cache_3247_, 0);
v_funInfo_3256_ = lean_ctor_get(v_cache_3247_, 1);
v_synthInstance_3257_ = lean_ctor_get(v_cache_3247_, 2);
v_whnf_3258_ = lean_ctor_get(v_cache_3247_, 3);
v_defEqTrans_3259_ = lean_ctor_get(v_cache_3247_, 4);
v_defEqPerm_3260_ = lean_ctor_get(v_cache_3247_, 5);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_cache_3247_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3262_ = v_cache_3247_;
v_isShared_3263_ = v_isSharedCheck_3275_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_defEqPerm_3260_);
lean_inc(v_defEqTrans_3259_);
lean_inc(v_whnf_3258_);
lean_inc(v_synthInstance_3257_);
lean_inc(v_funInfo_3256_);
lean_inc(v_inferType_3255_);
lean_dec(v_cache_3247_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3275_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
lean_inc(v_a_3241_);
v___x_3264_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3255_, v_a_3235_, v_a_3241_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3264_);
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_funInfo_3256_);
lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_synthInstance_3257_);
lean_ctor_set(v_reuseFailAlloc_3274_, 3, v_whnf_3258_);
lean_ctor_set(v_reuseFailAlloc_3274_, 4, v_defEqTrans_3259_);
lean_ctor_set(v_reuseFailAlloc_3274_, 5, v_defEqPerm_3260_);
v___x_3266_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3268_; 
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 1, v___x_3266_);
v___x_3268_ = v___x_3253_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_mctx_3248_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3273_, 2, v_zetaDeltaFVarIds_3249_);
lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_postponed_3250_);
lean_ctor_set(v_reuseFailAlloc_3273_, 4, v_diag_3251_);
v___x_3268_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3269_ = lean_st_ref_put(v_a_3163_, v___x_3268_);
if (v_isShared_3245_ == 0)
{
v___x_3271_ = v___x_3244_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3241_);
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
}
}
}
else
{
lean_dec(v_a_3235_);
return v___x_3240_;
}
}
else
{
lean_dec(v_a_3235_);
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v_us_3214_);
lean_dec(v_declName_3213_);
v_a_3301_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3234_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3234_);
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
lean_dec_ref_known(v_e_3161_, 2);
goto v___jp_3215_;
}
}
}
v___jp_3215_:
{
lean_object* v_toCold_3216_; lean_object* v_cancelTk_x3f_3217_; 
v_toCold_3216_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3217_ = lean_ctor_get(v_toCold_3216_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3217_) == 1)
{
lean_object* v_val_3218_; uint8_t v___x_3219_; 
v_val_3218_ = lean_ctor_get(v_cancelTk_x3f_3217_, 0);
v___x_3219_ = l_IO_CancelToken_isSet(v_val_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3213_, v_us_3214_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_us_3214_);
lean_dec(v_declName_3213_);
v___x_3221_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
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
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3213_, v_us_3214_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3230_;
}
}
}
case 5:
{
lean_object* v_fn_3309_; uint8_t v_cacheInferType_3310_; lean_object* v_nargs_3311_; lean_object* v___x_3312_; lean_object* v_dummy_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_fn_3309_ = lean_ctor_get(v_e_3161_, 0);
v_cacheInferType_3310_ = lean_ctor_get_uint8(v_a_3162_, sizeof(void*)*7 + 3);
v_nargs_3311_ = l_Lean_Expr_getAppNumArgs(v_e_3161_);
v___x_3312_ = l_Lean_Expr_getAppFn(v_fn_3309_);
v_dummy_3313_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3311_);
v___x_3314_ = lean_mk_array(v_nargs_3311_, v_dummy_3313_);
v___x_3315_ = lean_unsigned_to_nat(1u);
v___x_3316_ = lean_nat_sub(v_nargs_3311_, v___x_3315_);
lean_dec(v_nargs_3311_);
lean_inc_ref(v_e_3161_);
v___x_3317_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3161_, v___x_3314_, v___x_3316_);
if (v_cacheInferType_3310_ == 0)
{
lean_dec_ref_known(v_e_3161_, 2);
goto v___jp_3318_;
}
else
{
uint8_t v___x_3334_; 
v___x_3334_ = l_Lean_Expr_hasMVar(v_e_3161_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3161_, v_a_3162_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3401_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3401_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3401_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3380_; lean_object* v_cache_3381_; lean_object* v_inferType_3382_; lean_object* v___x_3383_; 
v___x_3380_ = lean_st_ref_get(v_a_3163_);
v_cache_3381_ = lean_ctor_get(v___x_3380_, 1);
lean_inc_ref(v_cache_3381_);
lean_dec(v___x_3380_);
v_inferType_3382_ = lean_ctor_get(v_cache_3381_, 0);
lean_inc_ref(v_inferType_3382_);
lean_dec_ref(v_cache_3381_);
v___x_3383_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3382_, v_a_3336_);
lean_dec_ref(v_inferType_3382_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_toCold_3384_; lean_object* v_cancelTk_x3f_3385_; 
lean_del_object(v___x_3338_);
v_toCold_3384_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3385_ = lean_ctor_get(v_toCold_3384_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3385_) == 1)
{
lean_object* v_val_3386_; uint8_t v___x_3387_; 
v_val_3386_ = lean_ctor_get(v_cancelTk_x3f_3385_, 0);
v___x_3387_ = l_IO_CancelToken_isSet(v_val_3386_);
if (v___x_3387_ == 0)
{
goto v___jp_3340_;
}
else
{
lean_object* v___x_3388_; lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_a_3336_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3312_);
v___x_3388_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
goto v___jp_3340_;
}
}
else
{
lean_object* v_val_3397_; lean_object* v___x_3399_; 
lean_dec(v_a_3336_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3312_);
v_val_3397_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_val_3397_);
lean_dec_ref_known(v___x_3383_, 1);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v_val_3397_);
v___x_3399_ = v___x_3338_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_val_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
v___jp_3340_:
{
lean_object* v___x_3341_; 
v___x_3341_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3312_, v___x_3317_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
lean_dec_ref(v___x_3317_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; uint8_t v___x_3343_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v___x_3343_ = l_Lean_Expr_hasMVar(v_a_3342_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3378_; 
lean_inc(v_a_3342_);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3378_ == 0)
{
lean_object* v_unused_3379_; 
v_unused_3379_ = lean_ctor_get(v___x_3341_, 0);
lean_dec(v_unused_3379_);
v___x_3345_ = v___x_3341_;
v_isShared_3346_ = v_isSharedCheck_3378_;
goto v_resetjp_3344_;
}
else
{
lean_dec(v___x_3341_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3378_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v_cache_3348_; lean_object* v_mctx_3349_; lean_object* v_zetaDeltaFVarIds_3350_; lean_object* v_postponed_3351_; lean_object* v_diag_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3377_; 
v___x_3347_ = lean_st_ref_take(v_a_3163_);
v_cache_3348_ = lean_ctor_get(v___x_3347_, 1);
v_mctx_3349_ = lean_ctor_get(v___x_3347_, 0);
v_zetaDeltaFVarIds_3350_ = lean_ctor_get(v___x_3347_, 2);
v_postponed_3351_ = lean_ctor_get(v___x_3347_, 3);
v_diag_3352_ = lean_ctor_get(v___x_3347_, 4);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3354_ = v___x_3347_;
v_isShared_3355_ = v_isSharedCheck_3377_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_diag_3352_);
lean_inc(v_postponed_3351_);
lean_inc(v_zetaDeltaFVarIds_3350_);
lean_inc(v_cache_3348_);
lean_inc(v_mctx_3349_);
lean_dec(v___x_3347_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3377_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_inferType_3356_; lean_object* v_funInfo_3357_; lean_object* v_synthInstance_3358_; lean_object* v_whnf_3359_; lean_object* v_defEqTrans_3360_; lean_object* v_defEqPerm_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3376_; 
v_inferType_3356_ = lean_ctor_get(v_cache_3348_, 0);
v_funInfo_3357_ = lean_ctor_get(v_cache_3348_, 1);
v_synthInstance_3358_ = lean_ctor_get(v_cache_3348_, 2);
v_whnf_3359_ = lean_ctor_get(v_cache_3348_, 3);
v_defEqTrans_3360_ = lean_ctor_get(v_cache_3348_, 4);
v_defEqPerm_3361_ = lean_ctor_get(v_cache_3348_, 5);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_cache_3348_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3363_ = v_cache_3348_;
v_isShared_3364_ = v_isSharedCheck_3376_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_defEqPerm_3361_);
lean_inc(v_defEqTrans_3360_);
lean_inc(v_whnf_3359_);
lean_inc(v_synthInstance_3358_);
lean_inc(v_funInfo_3357_);
lean_inc(v_inferType_3356_);
lean_dec(v_cache_3348_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3376_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3367_; 
lean_inc(v_a_3342_);
v___x_3365_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3356_, v_a_3336_, v_a_3342_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3365_);
v___x_3367_ = v___x_3363_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3365_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v_funInfo_3357_);
lean_ctor_set(v_reuseFailAlloc_3375_, 2, v_synthInstance_3358_);
lean_ctor_set(v_reuseFailAlloc_3375_, 3, v_whnf_3359_);
lean_ctor_set(v_reuseFailAlloc_3375_, 4, v_defEqTrans_3360_);
lean_ctor_set(v_reuseFailAlloc_3375_, 5, v_defEqPerm_3361_);
v___x_3367_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 1, v___x_3367_);
v___x_3369_ = v___x_3354_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_mctx_3349_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_zetaDeltaFVarIds_3350_);
lean_ctor_set(v_reuseFailAlloc_3374_, 3, v_postponed_3351_);
lean_ctor_set(v_reuseFailAlloc_3374_, 4, v_diag_3352_);
v___x_3369_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_st_ref_put(v_a_3163_, v___x_3369_);
if (v_isShared_3346_ == 0)
{
v___x_3372_ = v___x_3345_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3342_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3336_);
return v___x_3341_;
}
}
else
{
lean_dec(v_a_3336_);
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3312_);
v_a_3402_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3335_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3335_);
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
lean_dec_ref_known(v_e_3161_, 2);
goto v___jp_3318_;
}
}
v___jp_3318_:
{
lean_object* v_toCold_3319_; lean_object* v_cancelTk_x3f_3320_; 
v_toCold_3319_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3320_ = lean_ctor_get(v_toCold_3319_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3320_) == 1)
{
lean_object* v_val_3321_; uint8_t v___x_3322_; 
v_val_3321_ = lean_ctor_get(v_cancelTk_x3f_3320_, 0);
v___x_3322_ = l_IO_CancelToken_isSet(v_val_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3312_, v___x_3317_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
lean_dec_ref(v___x_3317_);
return v___x_3323_;
}
else
{
lean_object* v___x_3324_; lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3312_);
v___x_3324_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3312_, v___x_3317_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
lean_dec_ref(v___x_3317_);
return v___x_3333_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3410_; 
v_cacheInferType_3410_ = lean_ctor_get_uint8(v_a_3162_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3410_ == 0)
{
goto v___jp_3183_;
}
else
{
uint8_t v___x_3411_; 
v___x_3411_ = l_Lean_Expr_hasMVar(v_e_3161_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
lean_inc_ref(v_e_3161_);
v___x_3412_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3161_, v_a_3162_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3478_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3478_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3478_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3457_; lean_object* v_cache_3458_; lean_object* v_inferType_3459_; lean_object* v___x_3460_; 
v___x_3457_ = lean_st_ref_get(v_a_3163_);
v_cache_3458_ = lean_ctor_get(v___x_3457_, 1);
lean_inc_ref(v_cache_3458_);
lean_dec(v___x_3457_);
v_inferType_3459_ = lean_ctor_get(v_cache_3458_, 0);
lean_inc_ref(v_inferType_3459_);
lean_dec_ref(v_cache_3458_);
v___x_3460_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3459_, v_a_3413_);
lean_dec_ref(v_inferType_3459_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_toCold_3461_; lean_object* v_cancelTk_x3f_3462_; 
lean_del_object(v___x_3415_);
v_toCold_3461_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3462_ = lean_ctor_get(v_toCold_3461_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3462_) == 1)
{
lean_object* v_val_3463_; uint8_t v___x_3464_; 
v_val_3463_ = lean_ctor_get(v_cancelTk_x3f_3462_, 0);
v___x_3464_ = l_IO_CancelToken_isSet(v_val_3463_);
if (v___x_3464_ == 0)
{
goto v___jp_3417_;
}
else
{
lean_object* v___x_3465_; lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_a_3413_);
lean_dec_ref_known(v_e_3161_, 3);
v___x_3465_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
goto v___jp_3417_;
}
}
else
{
lean_object* v_val_3474_; lean_object* v___x_3476_; 
lean_dec(v_a_3413_);
lean_dec_ref_known(v_e_3161_, 3);
v_val_3474_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_val_3474_);
lean_dec_ref_known(v___x_3460_, 1);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v_val_3474_);
v___x_3476_ = v___x_3415_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_val_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
v___jp_3417_:
{
lean_object* v___x_3418_; 
v___x_3418_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; uint8_t v___x_3420_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
v___x_3420_ = l_Lean_Expr_hasMVar(v_a_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3455_; 
lean_inc(v_a_3419_);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; 
v_unused_3456_ = lean_ctor_get(v___x_3418_, 0);
lean_dec(v_unused_3456_);
v___x_3422_ = v___x_3418_;
v_isShared_3423_ = v_isSharedCheck_3455_;
goto v_resetjp_3421_;
}
else
{
lean_dec(v___x_3418_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3455_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v_cache_3425_; lean_object* v_mctx_3426_; lean_object* v_zetaDeltaFVarIds_3427_; lean_object* v_postponed_3428_; lean_object* v_diag_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3454_; 
v___x_3424_ = lean_st_ref_take(v_a_3163_);
v_cache_3425_ = lean_ctor_get(v___x_3424_, 1);
v_mctx_3426_ = lean_ctor_get(v___x_3424_, 0);
v_zetaDeltaFVarIds_3427_ = lean_ctor_get(v___x_3424_, 2);
v_postponed_3428_ = lean_ctor_get(v___x_3424_, 3);
v_diag_3429_ = lean_ctor_get(v___x_3424_, 4);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3431_ = v___x_3424_;
v_isShared_3432_ = v_isSharedCheck_3454_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_diag_3429_);
lean_inc(v_postponed_3428_);
lean_inc(v_zetaDeltaFVarIds_3427_);
lean_inc(v_cache_3425_);
lean_inc(v_mctx_3426_);
lean_dec(v___x_3424_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3454_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_inferType_3433_; lean_object* v_funInfo_3434_; lean_object* v_synthInstance_3435_; lean_object* v_whnf_3436_; lean_object* v_defEqTrans_3437_; lean_object* v_defEqPerm_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3453_; 
v_inferType_3433_ = lean_ctor_get(v_cache_3425_, 0);
v_funInfo_3434_ = lean_ctor_get(v_cache_3425_, 1);
v_synthInstance_3435_ = lean_ctor_get(v_cache_3425_, 2);
v_whnf_3436_ = lean_ctor_get(v_cache_3425_, 3);
v_defEqTrans_3437_ = lean_ctor_get(v_cache_3425_, 4);
v_defEqPerm_3438_ = lean_ctor_get(v_cache_3425_, 5);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_cache_3425_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3440_ = v_cache_3425_;
v_isShared_3441_ = v_isSharedCheck_3453_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_defEqPerm_3438_);
lean_inc(v_defEqTrans_3437_);
lean_inc(v_whnf_3436_);
lean_inc(v_synthInstance_3435_);
lean_inc(v_funInfo_3434_);
lean_inc(v_inferType_3433_);
lean_dec(v_cache_3425_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3453_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
lean_inc(v_a_3419_);
v___x_3442_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3433_, v_a_3413_, v_a_3419_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3442_);
v___x_3444_ = v___x_3440_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_funInfo_3434_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_synthInstance_3435_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_whnf_3436_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_defEqTrans_3437_);
lean_ctor_set(v_reuseFailAlloc_3452_, 5, v_defEqPerm_3438_);
v___x_3444_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3444_);
v___x_3446_ = v___x_3431_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_mctx_3426_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_zetaDeltaFVarIds_3427_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_postponed_3428_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_diag_3429_);
v___x_3446_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3447_ = lean_st_ref_put(v_a_3163_, v___x_3446_);
if (v_isShared_3423_ == 0)
{
v___x_3449_ = v___x_3422_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3419_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3413_);
return v___x_3418_;
}
}
else
{
lean_dec(v_a_3413_);
return v___x_3418_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref_known(v_e_3161_, 3);
v_a_3479_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3412_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3412_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
goto v___jp_3183_;
}
}
}
case 9:
{
lean_object* v_a_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_a_3487_ = lean_ctor_get(v_e_3161_, 0);
lean_inc_ref(v_a_3487_);
lean_dec_ref_known(v_e_3161_, 1);
v___x_3488_ = l_Lean_Literal_type(v_a_3487_);
lean_dec_ref(v_a_3487_);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
case 10:
{
lean_object* v_expr_3490_; 
v_expr_3490_ = lean_ctor_get(v_e_3161_, 1);
lean_inc_ref(v_expr_3490_);
lean_dec_ref_known(v_e_3161_, 2);
v_e_3161_ = v_expr_3490_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3492_; lean_object* v_idx_3493_; lean_object* v_struct_3494_; uint8_t v_cacheInferType_3511_; 
v_typeName_3492_ = lean_ctor_get(v_e_3161_, 0);
lean_inc(v_typeName_3492_);
v_idx_3493_ = lean_ctor_get(v_e_3161_, 1);
lean_inc(v_idx_3493_);
v_struct_3494_ = lean_ctor_get(v_e_3161_, 2);
lean_inc_ref(v_struct_3494_);
v_cacheInferType_3511_ = lean_ctor_get_uint8(v_a_3162_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3511_ == 0)
{
lean_dec_ref_known(v_e_3161_, 3);
goto v___jp_3495_;
}
else
{
uint8_t v___x_3512_; 
v___x_3512_ = l_Lean_Expr_hasMVar(v_e_3161_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3161_, v_a_3162_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3579_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3579_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3579_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3558_; lean_object* v_cache_3559_; lean_object* v_inferType_3560_; lean_object* v___x_3561_; 
v___x_3558_ = lean_st_ref_get(v_a_3163_);
v_cache_3559_ = lean_ctor_get(v___x_3558_, 1);
lean_inc_ref(v_cache_3559_);
lean_dec(v___x_3558_);
v_inferType_3560_ = lean_ctor_get(v_cache_3559_, 0);
lean_inc_ref(v_inferType_3560_);
lean_dec_ref(v_cache_3559_);
v___x_3561_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3560_, v_a_3514_);
lean_dec_ref(v_inferType_3560_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_toCold_3562_; lean_object* v_cancelTk_x3f_3563_; 
lean_del_object(v___x_3516_);
v_toCold_3562_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3563_ = lean_ctor_get(v_toCold_3562_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3563_) == 1)
{
lean_object* v_val_3564_; uint8_t v___x_3565_; 
v_val_3564_ = lean_ctor_get(v_cancelTk_x3f_3563_, 0);
v___x_3565_ = l_IO_CancelToken_isSet(v_val_3564_);
if (v___x_3565_ == 0)
{
goto v___jp_3518_;
}
else
{
lean_object* v___x_3566_; lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_a_3514_);
lean_dec_ref(v_struct_3494_);
lean_dec(v_idx_3493_);
lean_dec(v_typeName_3492_);
v___x_3566_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
else
{
goto v___jp_3518_;
}
}
else
{
lean_object* v_val_3575_; lean_object* v___x_3577_; 
lean_dec(v_a_3514_);
lean_dec_ref(v_struct_3494_);
lean_dec(v_idx_3493_);
lean_dec(v_typeName_3492_);
v_val_3575_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_val_3575_);
lean_dec_ref_known(v___x_3561_, 1);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v_val_3575_);
v___x_3577_ = v___x_3516_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_val_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
v___jp_3518_:
{
lean_object* v___x_3519_; 
v___x_3519_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3492_, v_idx_3493_, v_struct_3494_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; uint8_t v___x_3521_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v___x_3521_ = l_Lean_Expr_hasMVar(v_a_3520_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3556_; 
lean_inc(v_a_3520_);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v___x_3519_, 0);
lean_dec(v_unused_3557_);
v___x_3523_ = v___x_3519_;
v_isShared_3524_ = v_isSharedCheck_3556_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v___x_3519_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3556_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v_cache_3526_; lean_object* v_mctx_3527_; lean_object* v_zetaDeltaFVarIds_3528_; lean_object* v_postponed_3529_; lean_object* v_diag_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3555_; 
v___x_3525_ = lean_st_ref_take(v_a_3163_);
v_cache_3526_ = lean_ctor_get(v___x_3525_, 1);
v_mctx_3527_ = lean_ctor_get(v___x_3525_, 0);
v_zetaDeltaFVarIds_3528_ = lean_ctor_get(v___x_3525_, 2);
v_postponed_3529_ = lean_ctor_get(v___x_3525_, 3);
v_diag_3530_ = lean_ctor_get(v___x_3525_, 4);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3532_ = v___x_3525_;
v_isShared_3533_ = v_isSharedCheck_3555_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_diag_3530_);
lean_inc(v_postponed_3529_);
lean_inc(v_zetaDeltaFVarIds_3528_);
lean_inc(v_cache_3526_);
lean_inc(v_mctx_3527_);
lean_dec(v___x_3525_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3555_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v_inferType_3534_; lean_object* v_funInfo_3535_; lean_object* v_synthInstance_3536_; lean_object* v_whnf_3537_; lean_object* v_defEqTrans_3538_; lean_object* v_defEqPerm_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3554_; 
v_inferType_3534_ = lean_ctor_get(v_cache_3526_, 0);
v_funInfo_3535_ = lean_ctor_get(v_cache_3526_, 1);
v_synthInstance_3536_ = lean_ctor_get(v_cache_3526_, 2);
v_whnf_3537_ = lean_ctor_get(v_cache_3526_, 3);
v_defEqTrans_3538_ = lean_ctor_get(v_cache_3526_, 4);
v_defEqPerm_3539_ = lean_ctor_get(v_cache_3526_, 5);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_cache_3526_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3541_ = v_cache_3526_;
v_isShared_3542_ = v_isSharedCheck_3554_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_defEqPerm_3539_);
lean_inc(v_defEqTrans_3538_);
lean_inc(v_whnf_3537_);
lean_inc(v_synthInstance_3536_);
lean_inc(v_funInfo_3535_);
lean_inc(v_inferType_3534_);
lean_dec(v_cache_3526_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3554_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
lean_inc(v_a_3520_);
v___x_3543_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3534_, v_a_3514_, v_a_3520_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3543_);
v___x_3545_ = v___x_3541_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3543_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_funInfo_3535_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_synthInstance_3536_);
lean_ctor_set(v_reuseFailAlloc_3553_, 3, v_whnf_3537_);
lean_ctor_set(v_reuseFailAlloc_3553_, 4, v_defEqTrans_3538_);
lean_ctor_set(v_reuseFailAlloc_3553_, 5, v_defEqPerm_3539_);
v___x_3545_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3547_; 
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 1, v___x_3545_);
v___x_3547_ = v___x_3532_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_mctx_3527_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_zetaDeltaFVarIds_3528_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_postponed_3529_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_diag_3530_);
v___x_3547_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = lean_st_ref_put(v_a_3163_, v___x_3547_);
if (v_isShared_3524_ == 0)
{
v___x_3550_ = v___x_3523_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3520_);
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
}
}
}
else
{
lean_dec(v_a_3514_);
return v___x_3519_;
}
}
else
{
lean_dec(v_a_3514_);
return v___x_3519_;
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v_struct_3494_);
lean_dec(v_idx_3493_);
lean_dec(v_typeName_3492_);
v_a_3580_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3513_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3513_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3161_, 3);
goto v___jp_3495_;
}
}
v___jp_3495_:
{
lean_object* v_toCold_3496_; lean_object* v_cancelTk_x3f_3497_; 
v_toCold_3496_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3497_ = lean_ctor_get(v_toCold_3496_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3497_) == 1)
{
lean_object* v_val_3498_; uint8_t v___x_3499_; 
v_val_3498_ = lean_ctor_get(v_cancelTk_x3f_3497_, 0);
v___x_3499_ = l_IO_CancelToken_isSet(v_val_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
v___x_3500_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3492_, v_idx_3493_, v_struct_3494_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3500_;
}
else
{
lean_object* v___x_3501_; lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_struct_3494_);
lean_dec(v_idx_3493_);
lean_dec(v_typeName_3492_);
v___x_3501_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
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
else
{
lean_object* v___x_3510_; 
v___x_3510_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3492_, v_idx_3493_, v_struct_3494_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3510_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3588_; 
v_cacheInferType_3588_ = lean_ctor_get_uint8(v_a_3162_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3588_ == 0)
{
goto v___jp_3167_;
}
else
{
uint8_t v___x_3589_; 
v___x_3589_ = l_Lean_Expr_hasMVar(v_e_3161_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; 
lean_inc_ref(v_e_3161_);
v___x_3590_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3161_, v_a_3162_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3656_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3656_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3656_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3635_; lean_object* v_cache_3636_; lean_object* v_inferType_3637_; lean_object* v___x_3638_; 
v___x_3635_ = lean_st_ref_get(v_a_3163_);
v_cache_3636_ = lean_ctor_get(v___x_3635_, 1);
lean_inc_ref(v_cache_3636_);
lean_dec(v___x_3635_);
v_inferType_3637_ = lean_ctor_get(v_cache_3636_, 0);
lean_inc_ref(v_inferType_3637_);
lean_dec_ref(v_cache_3636_);
v___x_3638_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3637_, v_a_3591_);
lean_dec_ref(v_inferType_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_toCold_3639_; lean_object* v_cancelTk_x3f_3640_; 
lean_del_object(v___x_3593_);
v_toCold_3639_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3640_ = lean_ctor_get(v_toCold_3639_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3640_) == 1)
{
lean_object* v_val_3641_; uint8_t v___x_3642_; 
v_val_3641_ = lean_ctor_get(v_cancelTk_x3f_3640_, 0);
v___x_3642_ = l_IO_CancelToken_isSet(v_val_3641_);
if (v___x_3642_ == 0)
{
goto v___jp_3595_;
}
else
{
lean_object* v___x_3643_; lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_e_3161_);
v___x_3643_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
else
{
goto v___jp_3595_;
}
}
else
{
lean_object* v_val_3652_; lean_object* v___x_3654_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_e_3161_);
v_val_3652_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_val_3652_);
lean_dec_ref_known(v___x_3638_, 1);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v_val_3652_);
v___x_3654_ = v___x_3593_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_val_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
v___jp_3595_:
{
lean_object* v___x_3596_; 
v___x_3596_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; uint8_t v___x_3598_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v___x_3598_ = l_Lean_Expr_hasMVar(v_a_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3633_; 
lean_inc(v_a_3597_);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v___x_3596_, 0);
lean_dec(v_unused_3634_);
v___x_3600_ = v___x_3596_;
v_isShared_3601_ = v_isSharedCheck_3633_;
goto v_resetjp_3599_;
}
else
{
lean_dec(v___x_3596_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3633_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v_cache_3603_; lean_object* v_mctx_3604_; lean_object* v_zetaDeltaFVarIds_3605_; lean_object* v_postponed_3606_; lean_object* v_diag_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3632_; 
v___x_3602_ = lean_st_ref_take(v_a_3163_);
v_cache_3603_ = lean_ctor_get(v___x_3602_, 1);
v_mctx_3604_ = lean_ctor_get(v___x_3602_, 0);
v_zetaDeltaFVarIds_3605_ = lean_ctor_get(v___x_3602_, 2);
v_postponed_3606_ = lean_ctor_get(v___x_3602_, 3);
v_diag_3607_ = lean_ctor_get(v___x_3602_, 4);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3609_ = v___x_3602_;
v_isShared_3610_ = v_isSharedCheck_3632_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_diag_3607_);
lean_inc(v_postponed_3606_);
lean_inc(v_zetaDeltaFVarIds_3605_);
lean_inc(v_cache_3603_);
lean_inc(v_mctx_3604_);
lean_dec(v___x_3602_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3632_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v_inferType_3611_; lean_object* v_funInfo_3612_; lean_object* v_synthInstance_3613_; lean_object* v_whnf_3614_; lean_object* v_defEqTrans_3615_; lean_object* v_defEqPerm_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3631_; 
v_inferType_3611_ = lean_ctor_get(v_cache_3603_, 0);
v_funInfo_3612_ = lean_ctor_get(v_cache_3603_, 1);
v_synthInstance_3613_ = lean_ctor_get(v_cache_3603_, 2);
v_whnf_3614_ = lean_ctor_get(v_cache_3603_, 3);
v_defEqTrans_3615_ = lean_ctor_get(v_cache_3603_, 4);
v_defEqPerm_3616_ = lean_ctor_get(v_cache_3603_, 5);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_cache_3603_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3618_ = v_cache_3603_;
v_isShared_3619_ = v_isSharedCheck_3631_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_defEqPerm_3616_);
lean_inc(v_defEqTrans_3615_);
lean_inc(v_whnf_3614_);
lean_inc(v_synthInstance_3613_);
lean_inc(v_funInfo_3612_);
lean_inc(v_inferType_3611_);
lean_dec(v_cache_3603_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3631_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_inc(v_a_3597_);
v___x_3620_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3611_, v_a_3591_, v_a_3597_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v___x_3620_);
v___x_3622_ = v___x_3618_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_funInfo_3612_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_synthInstance_3613_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_whnf_3614_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_defEqTrans_3615_);
lean_ctor_set(v_reuseFailAlloc_3630_, 5, v_defEqPerm_3616_);
v___x_3622_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3624_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 1, v___x_3622_);
v___x_3624_ = v___x_3609_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_mctx_3604_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_zetaDeltaFVarIds_3605_);
lean_ctor_set(v_reuseFailAlloc_3629_, 3, v_postponed_3606_);
lean_ctor_set(v_reuseFailAlloc_3629_, 4, v_diag_3607_);
v___x_3624_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3625_; lean_object* v___x_3627_; 
v___x_3625_ = lean_st_ref_put(v_a_3163_, v___x_3624_);
if (v_isShared_3601_ == 0)
{
v___x_3627_ = v___x_3600_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3597_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3591_);
return v___x_3596_;
}
}
else
{
lean_dec(v_a_3591_);
return v___x_3596_;
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec_ref(v_e_3161_);
v_a_3657_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3590_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3590_);
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
goto v___jp_3167_;
}
}
}
}
v___jp_3167_:
{
lean_object* v_toCold_3168_; lean_object* v_cancelTk_x3f_3169_; 
v_toCold_3168_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3169_ = lean_ctor_get(v_toCold_3168_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3169_) == 1)
{
lean_object* v_val_3170_; uint8_t v___x_3171_; 
v_val_3170_ = lean_ctor_get(v_cancelTk_x3f_3169_, 0);
v___x_3171_ = l_IO_CancelToken_isSet(v_val_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3172_;
}
else
{
lean_object* v___x_3173_; lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v_e_3161_);
v___x_3173_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
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
lean_object* v___x_3182_; 
v___x_3182_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3182_;
}
}
v___jp_3183_:
{
lean_object* v_toCold_3184_; lean_object* v_cancelTk_x3f_3185_; 
v_toCold_3184_ = lean_ctor_get(v_a_3164_, 0);
v_cancelTk_x3f_3185_ = lean_ctor_get(v_toCold_3184_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3185_) == 1)
{
lean_object* v_val_3186_; uint8_t v___x_3187_; 
v_val_3186_ = lean_ctor_get(v_cancelTk_x3f_3185_, 0);
v___x_3187_ = l_IO_CancelToken_isSet(v_val_3186_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v_e_3161_);
v___x_3189_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v___x_3198_; 
v___x_3198_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
return v___x_3198_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3161_ = stack[0].m_obj;
lean_object* v_a_3162_ = stack[1].m_obj;
lean_object* v_a_3163_ = stack[2].m_obj;
lean_object* v_a_3164_ = stack[3].m_obj;
lean_object* v_a_3165_ = stack[4].m_obj;
lean_object* v_res_3665_;
v_res_3665_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
stack->m_obj
 = v_res_3665_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3673_, lean_object* v_x_3674_, lean_object* v_x_3675_, lean_object* v_x_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3674_, v_x_3675_, v_x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3678_, lean_object* v_x_3679_, lean_object* v_x_3680_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3679_, v_x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3682_, lean_object* v_x_3683_, lean_object* v_x_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3682_, v_x_3683_, v_x_3684_);
lean_dec_ref(v_x_3684_);
lean_dec_ref(v_x_3683_);
return v_res_3685_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3686_, lean_object* v_x_3687_, size_t v_x_3688_, size_t v_x_3689_, lean_object* v_x_3690_, lean_object* v_x_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3687_, v_x_3688_, v_x_3689_, v_x_3690_, v_x_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3687_ = stack[1].m_obj;
size_t v_x_3688_ = stack[2].m_num;
size_t v_x_3689_ = stack[3].m_num;
lean_object* v_x_3690_ = stack[4].m_obj;
lean_object* v_x_3691_ = stack[5].m_obj;
lean_object* v_res_3693_;
v_res_3693_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_box(0), v_x_3687_, v_x_3688_, v_x_3689_, v_x_3690_, v_x_3691_);
stack->m_obj
 = v_res_3693_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3694_, lean_object* v_x_3695_, lean_object* v_x_3696_, lean_object* v_x_3697_, lean_object* v_x_3698_, lean_object* v_x_3699_){
_start:
{
size_t v_x_4307__boxed_3700_; size_t v_x_4308__boxed_3701_; lean_object* v_res_3702_; 
v_x_4307__boxed_3700_ = lean_unbox_usize(v_x_3696_);
lean_dec(v_x_3696_);
v_x_4308__boxed_3701_ = lean_unbox_usize(v_x_3697_);
lean_dec(v_x_3697_);
v_res_3702_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3694_, v_x_3695_, v_x_4307__boxed_3700_, v_x_4308__boxed_3701_, v_x_3698_, v_x_3699_);
return v_res_3702_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3703_, lean_object* v_x_3704_, size_t v_x_3705_, lean_object* v_x_3706_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3704_, v_x_3705_, v_x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3704_ = stack[1].m_obj;
size_t v_x_3705_ = stack[2].m_num;
lean_object* v_x_3706_ = stack[3].m_obj;
lean_object* v_res_3708_;
v_res_3708_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_box(0), v_x_3704_, v_x_3705_, v_x_3706_);
stack->m_obj
 = v_res_3708_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3709_, lean_object* v_x_3710_, lean_object* v_x_3711_, lean_object* v_x_3712_){
_start:
{
size_t v_x_4335__boxed_3713_; lean_object* v_res_3714_; 
v_x_4335__boxed_3713_ = lean_unbox_usize(v_x_3711_);
lean_dec(v_x_3711_);
v_res_3714_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3709_, v_x_3710_, v_x_4335__boxed_3713_, v_x_3712_);
lean_dec_ref(v_x_3712_);
lean_dec_ref(v_x_3710_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3715_, lean_object* v_n_3716_, lean_object* v_k_3717_, lean_object* v_v_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3716_, v_k_3717_, v_v_3718_);
return v___x_3719_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3720_, size_t v_depth_3721_, lean_object* v_keys_3722_, lean_object* v_vals_3723_, lean_object* v_heq_3724_, lean_object* v_i_3725_, lean_object* v_entries_3726_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3721_, v_keys_3722_, v_vals_3723_, v_i_3725_, v_entries_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3721_ = stack[1].m_num;
lean_object* v_keys_3722_ = stack[2].m_obj;
lean_object* v_vals_3723_ = stack[3].m_obj;
lean_object* v_i_3725_ = stack[5].m_obj;
lean_object* v_entries_3726_ = stack[6].m_obj;
lean_object* v_res_3728_;
v_res_3728_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_box(0), v_depth_3721_, v_keys_3722_, v_vals_3723_, lean_box(0), v_i_3725_, v_entries_3726_);
stack->m_obj
 = v_res_3728_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3729_, lean_object* v_depth_3730_, lean_object* v_keys_3731_, lean_object* v_vals_3732_, lean_object* v_heq_3733_, lean_object* v_i_3734_, lean_object* v_entries_3735_){
_start:
{
size_t v_depth_boxed_3736_; lean_object* v_res_3737_; 
v_depth_boxed_3736_ = lean_unbox_usize(v_depth_3730_);
lean_dec(v_depth_3730_);
v_res_3737_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3729_, v_depth_boxed_3736_, v_keys_3731_, v_vals_3732_, v_heq_3733_, v_i_3734_, v_entries_3735_);
lean_dec_ref(v_vals_3732_);
lean_dec_ref(v_keys_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3738_, lean_object* v_keys_3739_, lean_object* v_vals_3740_, lean_object* v_heq_3741_, lean_object* v_i_3742_, lean_object* v_k_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3739_, v_vals_3740_, v_i_3742_, v_k_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3745_, lean_object* v_keys_3746_, lean_object* v_vals_3747_, lean_object* v_heq_3748_, lean_object* v_i_3749_, lean_object* v_k_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3745_, v_keys_3746_, v_vals_3747_, v_heq_3748_, v_i_3749_, v_k_3750_);
lean_dec_ref(v_k_3750_);
lean_dec_ref(v_vals_3747_);
lean_dec_ref(v_keys_3746_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3752_, lean_object* v_x_3753_, lean_object* v_x_3754_, lean_object* v_x_3755_, lean_object* v_x_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3753_, v_x_3754_, v_x_3755_, v_x_3756_);
return v___x_3757_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = l_Lean_maxRecDepthErrorMessage;
v___x_3764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3766_ = l_Lean_MessageData_ofFormat(v___x_3765_);
return v___x_3766_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3767_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3768_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3769_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
lean_ctor_set(v___x_3769_, 1, v___x_3767_);
return v___x_3769_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3770_){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v_ref_3770_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3770_ = stack[0].m_obj;
lean_object* v_res_3775_;
v_res_3775_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3770_);
stack->m_obj
 = v_res_3775_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3776_);
return v_res_3778_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3779_, lean_object* v_ref_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3780_);
return v___x_3786_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3780_ = stack[1].m_obj;
lean_object* v___y_3781_ = stack[2].m_obj;
lean_object* v___y_3782_ = stack[3].m_obj;
lean_object* v___y_3783_ = stack[4].m_obj;
lean_object* v___y_3784_ = stack[5].m_obj;
lean_object* v_res_3787_;
v_res_3787_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_box(0), v_ref_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
stack->m_obj
 = v_res_3787_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3788_, lean_object* v_ref_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3788_, v_ref_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
return v_res_3795_;
}
}
lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3848_; uint8_t v_beta_3849_; 
v___x_3848_ = l_Lean_Meta_Context_config(v___y_3797_);
v_beta_3849_ = lean_ctor_get_uint8(v___x_3848_, 13);
if (v_beta_3849_ == 0)
{
lean_dec_ref(v___x_3848_);
goto v___jp_3802_;
}
else
{
uint8_t v_iota_3850_; 
v_iota_3850_ = lean_ctor_get_uint8(v___x_3848_, 12);
if (v_iota_3850_ == 0)
{
lean_dec_ref(v___x_3848_);
goto v___jp_3802_;
}
else
{
uint8_t v_zeta_3851_; 
v_zeta_3851_ = lean_ctor_get_uint8(v___x_3848_, 15);
if (v_zeta_3851_ == 0)
{
lean_dec_ref(v___x_3848_);
goto v___jp_3802_;
}
else
{
uint8_t v_zetaHave_3852_; 
v_zetaHave_3852_ = lean_ctor_get_uint8(v___x_3848_, 18);
if (v_zetaHave_3852_ == 0)
{
lean_dec_ref(v___x_3848_);
goto v___jp_3802_;
}
else
{
uint8_t v_zetaDelta_3853_; 
v_zetaDelta_3853_ = lean_ctor_get_uint8(v___x_3848_, 16);
if (v_zetaDelta_3853_ == 0)
{
lean_dec_ref(v___x_3848_);
goto v___jp_3802_;
}
else
{
uint8_t v_etaStruct_3854_; uint8_t v_proj_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_etaStruct_3854_ = lean_ctor_get_uint8(v___x_3848_, 10);
v_proj_3855_ = lean_ctor_get_uint8(v___x_3848_, 14);
lean_dec_ref(v___x_3848_);
v___x_3856_ = lean_box(v_proj_3855_);
v___x_3857_ = lean_obj_tag_nat(v___x_3856_);
lean_dec(v___x_3856_);
v___x_3858_ = lean_unsigned_to_nat(2u);
v___x_3859_ = lean_nat_dec_eq(v___x_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
goto v___jp_3802_;
}
else
{
uint8_t v___x_3860_; uint8_t v___x_3861_; 
v___x_3860_ = 0;
v___x_3861_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3854_, v___x_3860_);
if (v___x_3861_ == 0)
{
goto v___jp_3802_;
}
else
{
lean_object* v___x_3862_; 
v___x_3862_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec_ref(v___y_3797_);
return v___x_3862_;
}
}
}
}
}
}
}
v___jp_3802_:
{
lean_object* v___x_3803_; uint8_t v_foApprox_3804_; uint8_t v_ctxApprox_3805_; uint8_t v_quasiPatternApprox_3806_; uint8_t v_constApprox_3807_; uint8_t v_isDefEqStuckEx_3808_; uint8_t v_unificationHints_3809_; uint8_t v_proofIrrelevance_3810_; uint8_t v_assignSyntheticOpaque_3811_; uint8_t v_offsetCnstrs_3812_; uint8_t v_transparency_3813_; uint8_t v_univApprox_3814_; uint8_t v_zetaUnused_3815_; uint8_t v_canUnfoldPredicateConfig_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3847_; 
v___x_3803_ = l_Lean_Meta_Context_config(v___y_3797_);
v_foApprox_3804_ = lean_ctor_get_uint8(v___x_3803_, 0);
v_ctxApprox_3805_ = lean_ctor_get_uint8(v___x_3803_, 1);
v_quasiPatternApprox_3806_ = lean_ctor_get_uint8(v___x_3803_, 2);
v_constApprox_3807_ = lean_ctor_get_uint8(v___x_3803_, 3);
v_isDefEqStuckEx_3808_ = lean_ctor_get_uint8(v___x_3803_, 4);
v_unificationHints_3809_ = lean_ctor_get_uint8(v___x_3803_, 5);
v_proofIrrelevance_3810_ = lean_ctor_get_uint8(v___x_3803_, 6);
v_assignSyntheticOpaque_3811_ = lean_ctor_get_uint8(v___x_3803_, 7);
v_offsetCnstrs_3812_ = lean_ctor_get_uint8(v___x_3803_, 8);
v_transparency_3813_ = lean_ctor_get_uint8(v___x_3803_, 9);
v_univApprox_3814_ = lean_ctor_get_uint8(v___x_3803_, 11);
v_zetaUnused_3815_ = lean_ctor_get_uint8(v___x_3803_, 17);
v_canUnfoldPredicateConfig_3816_ = lean_ctor_get_uint8(v___x_3803_, 19);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3818_ = v___x_3803_;
v_isShared_3819_ = v_isSharedCheck_3847_;
goto v_resetjp_3817_;
}
else
{
lean_dec(v___x_3803_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3847_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
uint8_t v___x_3820_; uint8_t v___x_3821_; uint8_t v___x_3822_; lean_object* v___x_3824_; 
v___x_3820_ = 1;
v___x_3821_ = 0;
v___x_3822_ = 2;
if (v_isShared_3819_ == 0)
{
v___x_3824_ = v___x_3818_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 0, v_foApprox_3804_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 1, v_ctxApprox_3805_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 2, v_quasiPatternApprox_3806_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 3, v_constApprox_3807_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 4, v_isDefEqStuckEx_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 5, v_unificationHints_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 6, v_proofIrrelevance_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 7, v_assignSyntheticOpaque_3811_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 8, v_offsetCnstrs_3812_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 9, v_transparency_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 11, v_univApprox_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 17, v_zetaUnused_3815_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, 19, v_canUnfoldPredicateConfig_3816_);
v___x_3824_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
uint8_t v_trackZetaDelta_3825_; lean_object* v_zetaDeltaSet_3826_; lean_object* v_lctx_3827_; lean_object* v_localInstances_3828_; lean_object* v_defEqCtx_x3f_3829_; lean_object* v_synthPendingDepth_3830_; lean_object* v_customCanUnfoldPredicate_x3f_3831_; uint8_t v_univApprox_3832_; uint8_t v_inTypeClassResolution_3833_; uint8_t v_cacheInferType_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3844_; 
lean_ctor_set_uint8(v___x_3824_, 10, v___x_3821_);
lean_ctor_set_uint8(v___x_3824_, 12, v___x_3820_);
lean_ctor_set_uint8(v___x_3824_, 13, v___x_3820_);
lean_ctor_set_uint8(v___x_3824_, 14, v___x_3822_);
lean_ctor_set_uint8(v___x_3824_, 15, v___x_3820_);
lean_ctor_set_uint8(v___x_3824_, 16, v___x_3820_);
lean_ctor_set_uint8(v___x_3824_, 18, v___x_3820_);
v_trackZetaDelta_3825_ = lean_ctor_get_uint8(v___y_3797_, sizeof(void*)*7);
v_zetaDeltaSet_3826_ = lean_ctor_get(v___y_3797_, 1);
v_lctx_3827_ = lean_ctor_get(v___y_3797_, 2);
v_localInstances_3828_ = lean_ctor_get(v___y_3797_, 3);
v_defEqCtx_x3f_3829_ = lean_ctor_get(v___y_3797_, 4);
v_synthPendingDepth_3830_ = lean_ctor_get(v___y_3797_, 5);
v_customCanUnfoldPredicate_x3f_3831_ = lean_ctor_get(v___y_3797_, 6);
v_univApprox_3832_ = lean_ctor_get_uint8(v___y_3797_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3833_ = lean_ctor_get_uint8(v___y_3797_, sizeof(void*)*7 + 2);
v_cacheInferType_3834_ = lean_ctor_get_uint8(v___y_3797_, sizeof(void*)*7 + 3);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___y_3797_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; 
v_unused_3845_ = lean_ctor_get(v___y_3797_, 0);
lean_dec(v_unused_3845_);
v___x_3836_ = v___y_3797_;
v_isShared_3837_ = v_isSharedCheck_3844_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3831_);
lean_inc(v_synthPendingDepth_3830_);
lean_inc(v_defEqCtx_x3f_3829_);
lean_inc(v_localInstances_3828_);
lean_inc(v_lctx_3827_);
lean_inc(v_zetaDeltaSet_3826_);
lean_dec(v___y_3797_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3844_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
uint64_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3841_; 
v___x_3838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3824_);
v___x_3839_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3839_, 0, v___x_3824_);
lean_ctor_set_uint64(v___x_3839_, sizeof(void*)*1, v___x_3838_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3839_);
v___x_3841_ = v___x_3836_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_zetaDeltaSet_3826_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_lctx_3827_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v_localInstances_3828_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v_defEqCtx_x3f_3829_);
lean_ctor_set(v_reuseFailAlloc_3843_, 5, v_synthPendingDepth_3830_);
lean_ctor_set(v_reuseFailAlloc_3843_, 6, v_customCanUnfoldPredicate_x3f_3831_);
lean_ctor_set_uint8(v_reuseFailAlloc_3843_, sizeof(void*)*7, v_trackZetaDelta_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3843_, sizeof(void*)*7 + 1, v_univApprox_3832_);
lean_ctor_set_uint8(v_reuseFailAlloc_3843_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3833_);
lean_ctor_set_uint8(v_reuseFailAlloc_3843_, sizeof(void*)*7 + 3, v_cacheInferType_3834_);
v___x_3841_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; 
v___x_3842_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3796_, v___x_3841_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec_ref(v___x_3841_);
return v___x_3842_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_inferTypeImp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3796_ = stack[0].m_obj;
lean_object* v___y_3797_ = stack[1].m_obj;
lean_object* v___y_3798_ = stack[2].m_obj;
lean_object* v___y_3799_ = stack[3].m_obj;
lean_object* v___y_3800_ = stack[4].m_obj;
lean_object* v_res_3863_;
v_res_3863_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
stack->m_obj
 = v_res_3863_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
return v_res_3870_;
}
}
lean_object* lean_infer_type(lean_object* v_e_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___y_3878_; lean_object* v_toCold_3895_; lean_object* v_currRecDepth_3896_; lean_object* v_ref_3897_; uint16_t v_optionFlags_3898_; uint8_t v_suppressElabErrors_3899_; uint8_t v_isRecordingDeps_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3940_; 
v_toCold_3895_ = lean_ctor_get(v_a_3874_, 0);
v_currRecDepth_3896_ = lean_ctor_get(v_a_3874_, 1);
v_ref_3897_ = lean_ctor_get(v_a_3874_, 2);
v_optionFlags_3898_ = lean_ctor_get_uint16(v_a_3874_, sizeof(void*)*3);
v_suppressElabErrors_3899_ = lean_ctor_get_uint8(v_a_3874_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3900_ = lean_ctor_get_uint8(v_a_3874_, sizeof(void*)*3 + 3);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_a_3874_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3902_ = v_a_3874_;
v_isShared_3903_ = v_isSharedCheck_3940_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_ref_3897_);
lean_inc(v_currRecDepth_3896_);
lean_inc(v_toCold_3895_);
lean_dec(v_a_3874_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3940_;
goto v_resetjp_3901_;
}
v___jp_3877_:
{
if (lean_obj_tag(v___y_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_a_3879_ = lean_ctor_get(v___y_3878_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___y_3878_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___y_3878_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___y_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
v_a_3887_ = lean_ctor_get(v___y_3878_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___y_3878_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___y_3878_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___y_3878_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
v_resetjp_3901_:
{
lean_object* v_maxRecDepth_3904_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
v_maxRecDepth_3904_ = lean_ctor_get(v_toCold_3895_, 3);
v___x_3936_ = lean_unsigned_to_nat(0u);
v___x_3937_ = lean_nat_dec_eq(v_maxRecDepth_3904_, v___x_3936_);
if (v___x_3937_ == 0)
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_nat_dec_eq(v_currRecDepth_3896_, v_maxRecDepth_3904_);
if (v___x_3938_ == 0)
{
goto v___jp_3905_;
}
else
{
lean_object* v___x_3939_; 
lean_del_object(v___x_3902_);
lean_dec(v_currRecDepth_3896_);
lean_dec_ref(v_toCold_3895_);
lean_dec(v_a_3875_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec_ref(v_e_3871_);
v___x_3939_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3897_);
return v___x_3939_;
}
}
else
{
goto v___jp_3905_;
}
v___jp_3905_:
{
lean_object* v___x_3906_; uint8_t v_transparency_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3906_ = l_Lean_Meta_Context_config(v_a_3872_);
v_transparency_3907_ = lean_ctor_get_uint8(v___x_3906_, 9);
lean_dec_ref(v___x_3906_);
v___x_3908_ = lean_unsigned_to_nat(1u);
v___x_3909_ = lean_nat_add(v_currRecDepth_3896_, v___x_3908_);
lean_dec(v_currRecDepth_3896_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 1, v___x_3909_);
v___x_3911_ = v___x_3902_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_toCold_3895_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_ref_3897_);
lean_ctor_set_uint16(v_reuseFailAlloc_3935_, sizeof(void*)*3, v_optionFlags_3898_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*3 + 2, v_suppressElabErrors_3899_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*3 + 3, v_isRecordingDeps_3900_);
v___x_3911_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
uint8_t v___x_3912_; uint8_t v___x_3913_; 
v___x_3912_ = 1;
v___x_3913_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3907_, v___x_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3871_, v_a_3872_, v_a_3873_, v___x_3911_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v___x_3911_);
lean_dec(v_a_3873_);
v___y_3878_ = v___x_3914_;
goto v___jp_3877_;
}
else
{
lean_object* v_keyedConfig_3915_; uint8_t v_trackZetaDelta_3916_; lean_object* v_zetaDeltaSet_3917_; lean_object* v_lctx_3918_; lean_object* v_localInstances_3919_; lean_object* v_defEqCtx_x3f_3920_; lean_object* v_synthPendingDepth_3921_; lean_object* v_customCanUnfoldPredicate_x3f_3922_; uint8_t v_univApprox_3923_; uint8_t v_inTypeClassResolution_3924_; uint8_t v_cacheInferType_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3934_; 
v_keyedConfig_3915_ = lean_ctor_get(v_a_3872_, 0);
v_trackZetaDelta_3916_ = lean_ctor_get_uint8(v_a_3872_, sizeof(void*)*7);
v_zetaDeltaSet_3917_ = lean_ctor_get(v_a_3872_, 1);
v_lctx_3918_ = lean_ctor_get(v_a_3872_, 2);
v_localInstances_3919_ = lean_ctor_get(v_a_3872_, 3);
v_defEqCtx_x3f_3920_ = lean_ctor_get(v_a_3872_, 4);
v_synthPendingDepth_3921_ = lean_ctor_get(v_a_3872_, 5);
v_customCanUnfoldPredicate_x3f_3922_ = lean_ctor_get(v_a_3872_, 6);
v_univApprox_3923_ = lean_ctor_get_uint8(v_a_3872_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3924_ = lean_ctor_get_uint8(v_a_3872_, sizeof(void*)*7 + 2);
v_cacheInferType_3925_ = lean_ctor_get_uint8(v_a_3872_, sizeof(void*)*7 + 3);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_a_3872_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3927_ = v_a_3872_;
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3922_);
lean_inc(v_synthPendingDepth_3921_);
lean_inc(v_defEqCtx_x3f_3920_);
lean_inc(v_localInstances_3919_);
lean_inc(v_lctx_3918_);
lean_inc(v_zetaDeltaSet_3917_);
lean_inc(v_keyedConfig_3915_);
lean_dec(v_a_3872_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3934_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3912_, v_keyedConfig_3915_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3929_);
v___x_3931_ = v___x_3927_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_zetaDeltaSet_3917_);
lean_ctor_set(v_reuseFailAlloc_3933_, 2, v_lctx_3918_);
lean_ctor_set(v_reuseFailAlloc_3933_, 3, v_localInstances_3919_);
lean_ctor_set(v_reuseFailAlloc_3933_, 4, v_defEqCtx_x3f_3920_);
lean_ctor_set(v_reuseFailAlloc_3933_, 5, v_synthPendingDepth_3921_);
lean_ctor_set(v_reuseFailAlloc_3933_, 6, v_customCanUnfoldPredicate_x3f_3922_);
lean_ctor_set_uint8(v_reuseFailAlloc_3933_, sizeof(void*)*7, v_trackZetaDelta_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3933_, sizeof(void*)*7 + 1, v_univApprox_3923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3933_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3924_);
lean_ctor_set_uint8(v_reuseFailAlloc_3933_, sizeof(void*)*7 + 3, v_cacheInferType_3925_);
v___x_3931_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3871_, v___x_3931_, v_a_3873_, v___x_3911_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v___x_3911_);
lean_dec(v_a_3873_);
v___y_3878_ = v___x_3932_;
goto v___jp_3877_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void lean_infer_type_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3871_ = stack[0].m_obj;
lean_object* v_a_3872_ = stack[1].m_obj;
lean_object* v_a_3873_ = stack[2].m_obj;
lean_object* v_a_3874_ = stack[3].m_obj;
lean_object* v_a_3875_ = stack[4].m_obj;
lean_object* v_res_3941_;
v_res_3941_ = lean_infer_type(v_e_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
stack->m_obj
 = v_res_3941_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = lean_infer_type(v_e_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_);
return v_res_3948_;
}
}
uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3949_){
_start:
{
switch(lean_obj_tag(v_x_3949_))
{
case 0:
{
uint8_t v___x_3950_; 
v___x_3950_ = 1;
return v___x_3950_;
}
case 2:
{
lean_object* v_a_3951_; lean_object* v_a_3952_; uint8_t v___x_3953_; 
v_a_3951_ = lean_ctor_get(v_x_3949_, 0);
v_a_3952_ = lean_ctor_get(v_x_3949_, 1);
v___x_3953_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3951_);
if (v___x_3953_ == 0)
{
return v___x_3953_;
}
else
{
v_x_3949_ = v_a_3952_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3955_; 
v_a_3955_ = lean_ctor_get(v_x_3949_, 1);
v_x_3949_ = v_a_3955_;
goto _start;
}
default: 
{
uint8_t v___x_3957_; 
v___x_3957_ = 0;
return v___x_3957_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3949_ = stack[0].m_obj;
uint8_t v_res_3958_;
v_res_3958_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3949_);
stack->m_num = v_res_3958_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3959_){
_start:
{
uint8_t v_res_3960_; lean_object* v_r_3961_; 
v_res_3960_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3959_);
lean_dec(v_x_3959_);
v_r_3961_ = lean_box(v_res_3960_);
return v_r_3961_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; lean_object* v_mctx_3966_; lean_object* v___x_3967_; lean_object* v_fst_3968_; lean_object* v_snd_3969_; lean_object* v___x_3970_; lean_object* v_cache_3971_; lean_object* v_zetaDeltaFVarIds_3972_; lean_object* v_postponed_3973_; lean_object* v_diag_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3983_; 
v___x_3965_ = lean_st_ref_get(v___y_3963_);
v_mctx_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc_ref(v_mctx_3966_);
lean_dec(v___x_3965_);
v___x_3967_ = lean_instantiate_level_mvars(v_mctx_3966_, v_l_3962_);
v_fst_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_fst_3968_);
v_snd_3969_ = lean_ctor_get(v___x_3967_, 1);
lean_inc(v_snd_3969_);
lean_dec_ref(v___x_3967_);
v___x_3970_ = lean_st_ref_take(v___y_3963_);
v_cache_3971_ = lean_ctor_get(v___x_3970_, 1);
v_zetaDeltaFVarIds_3972_ = lean_ctor_get(v___x_3970_, 2);
v_postponed_3973_ = lean_ctor_get(v___x_3970_, 3);
v_diag_3974_ = lean_ctor_get(v___x_3970_, 4);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; 
v_unused_3984_ = lean_ctor_get(v___x_3970_, 0);
lean_dec(v_unused_3984_);
v___x_3976_ = v___x_3970_;
v_isShared_3977_ = v_isSharedCheck_3983_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_diag_3974_);
lean_inc(v_postponed_3973_);
lean_inc(v_zetaDeltaFVarIds_3972_);
lean_inc(v_cache_3971_);
lean_dec(v___x_3970_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3983_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v_fst_3968_);
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_fst_3968_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_cache_3971_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_zetaDeltaFVarIds_3972_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_postponed_3973_);
lean_ctor_set(v_reuseFailAlloc_3982_, 4, v_diag_3974_);
v___x_3979_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_st_ref_put(v___y_3963_, v___x_3979_);
v___x_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3981_, 0, v_snd_3969_);
return v___x_3981_;
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_3962_ = stack[0].m_obj;
lean_object* v___y_3963_ = stack[1].m_obj;
lean_object* v_res_3985_;
v_res_3985_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3962_, v___y_3963_);
stack->m_obj
 = v_res_3985_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3986_, v___y_3987_);
lean_dec(v___y_3987_);
return v_res_3989_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3990_, v___y_3992_);
return v___x_3996_;
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_3990_ = stack[0].m_obj;
lean_object* v___y_3991_ = stack[1].m_obj;
lean_object* v___y_3992_ = stack[2].m_obj;
lean_object* v___y_3993_ = stack[3].m_obj;
lean_object* v___y_3994_ = stack[4].m_obj;
lean_object* v_res_3997_;
v_res_3997_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
stack->m_obj
 = v_res_3997_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
return v_res_4004_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_4005_, lean_object* v_x_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_){
_start:
{
switch(lean_obj_tag(v_x_4005_))
{
case 3:
{
lean_object* v_u_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; 
v_u_4016_ = lean_ctor_get(v_x_4005_, 0);
lean_inc(v_u_4016_);
lean_dec_ref_known(v_x_4005_, 1);
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = lean_nat_dec_eq(v_x_4006_, v___x_4017_);
lean_dec(v_x_4006_);
if (v___x_4018_ == 0)
{
lean_dec(v_u_4016_);
goto v___jp_4012_;
}
else
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4016_, v_a_4008_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4030_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4030_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4030_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
uint8_t v___x_4024_; uint8_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4024_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4020_);
lean_dec(v_a_4020_);
v___x_4025_ = l_Lean_Bool_toLBool(v___x_4024_);
v___x_4026_ = lean_box(v___x_4025_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v___x_4026_);
v___x_4028_ = v___x_4022_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
v_a_4031_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4019_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4019_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
case 7:
{
lean_object* v_body_4039_; lean_object* v_zero_4040_; uint8_t v_isZero_4041_; 
v_body_4039_ = lean_ctor_get(v_x_4005_, 2);
lean_inc_ref(v_body_4039_);
lean_dec_ref_known(v_x_4005_, 3);
v_zero_4040_ = lean_unsigned_to_nat(0u);
v_isZero_4041_ = lean_nat_dec_eq(v_x_4006_, v_zero_4040_);
if (v_isZero_4041_ == 1)
{
uint8_t v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
lean_dec_ref(v_body_4039_);
lean_dec(v_x_4006_);
v___x_4042_ = 0;
v___x_4043_ = lean_box(v___x_4042_);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
return v___x_4044_;
}
else
{
lean_object* v_one_4045_; lean_object* v_n_4046_; 
v_one_4045_ = lean_unsigned_to_nat(1u);
v_n_4046_ = lean_nat_sub(v_x_4006_, v_one_4045_);
lean_dec(v_x_4006_);
v_x_4005_ = v_body_4039_;
v_x_4006_ = v_n_4046_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4048_; 
v_body_4048_ = lean_ctor_get(v_x_4005_, 3);
lean_inc_ref(v_body_4048_);
lean_dec_ref_known(v_x_4005_, 4);
v_x_4005_ = v_body_4048_;
goto _start;
}
case 10:
{
lean_object* v_expr_4050_; 
v_expr_4050_ = lean_ctor_get(v_x_4005_, 1);
lean_inc_ref(v_expr_4050_);
lean_dec_ref_known(v_x_4005_, 2);
v_x_4005_ = v_expr_4050_;
goto _start;
}
default: 
{
lean_dec(v_x_4006_);
lean_dec_ref(v_x_4005_);
goto v___jp_4012_;
}
}
v___jp_4012_:
{
uint8_t v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4013_ = 2;
v___x_4014_ = lean_box(v___x_4013_);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
return v___x_4015_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4005_ = stack[0].m_obj;
lean_object* v_x_4006_ = stack[1].m_obj;
lean_object* v_a_4007_ = stack[2].m_obj;
lean_object* v_a_4008_ = stack[3].m_obj;
lean_object* v_a_4009_ = stack[4].m_obj;
lean_object* v_a_4010_ = stack[5].m_obj;
lean_object* v_res_4052_;
v_res_4052_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_4005_, v_x_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_);
stack->m_obj
 = v_res_4052_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_4053_, lean_object* v_x_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_4053_, v_x_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
return v_res_4060_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_4061_, lean_object* v_x_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
switch(lean_obj_tag(v_x_4061_))
{
case 4:
{
lean_object* v_declName_4068_; lean_object* v_us_4069_; lean_object* v___x_4070_; 
v_declName_4068_ = lean_ctor_get(v_x_4061_, 0);
lean_inc(v_declName_4068_);
v_us_4069_ = lean_ctor_get(v_x_4061_, 1);
lean_inc(v_us_4069_);
lean_dec_ref_known(v_x_4061_, 2);
v___x_4070_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4068_, v_us_4069_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v___x_4072_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4071_, v_x_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
return v___x_4072_;
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_x_4062_);
v_a_4073_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4070_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4070_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4081_; lean_object* v___x_4082_; 
v_fvarId_4081_ = lean_ctor_get(v_x_4061_, 0);
lean_inc(v_fvarId_4081_);
lean_dec_ref_known(v_x_4061_, 1);
v___x_4082_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4081_, v_a_4063_, v_a_4065_, v_a_4066_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4084_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4084_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4083_, v_x_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
return v___x_4084_;
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v_x_4062_);
v_a_4085_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4082_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4082_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4093_; lean_object* v___x_4094_; 
v_mvarId_4093_ = lean_ctor_get(v_x_4061_, 0);
lean_inc(v_mvarId_4093_);
lean_dec_ref_known(v_x_4061_, 1);
v___x_4094_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4093_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4096_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v___x_4096_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4095_, v_x_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
return v___x_4096_;
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_x_4062_);
v_a_4097_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4094_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4094_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
case 5:
{
lean_object* v_fn_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v_fn_4105_ = lean_ctor_get(v_x_4061_, 0);
lean_inc_ref(v_fn_4105_);
lean_dec_ref_known(v_x_4061_, 2);
v___x_4106_ = lean_unsigned_to_nat(1u);
v___x_4107_ = lean_nat_add(v_x_4062_, v___x_4106_);
lean_dec(v_x_4062_);
v_x_4061_ = v_fn_4105_;
v_x_4062_ = v___x_4107_;
goto _start;
}
case 10:
{
lean_object* v_expr_4109_; 
v_expr_4109_ = lean_ctor_get(v_x_4061_, 1);
lean_inc_ref(v_expr_4109_);
lean_dec_ref_known(v_x_4061_, 2);
v_x_4061_ = v_expr_4109_;
goto _start;
}
case 8:
{
lean_object* v_body_4111_; 
v_body_4111_ = lean_ctor_get(v_x_4061_, 3);
lean_inc_ref(v_body_4111_);
lean_dec_ref_known(v_x_4061_, 4);
v_x_4061_ = v_body_4111_;
goto _start;
}
case 6:
{
lean_object* v_body_4113_; lean_object* v_zero_4114_; uint8_t v_isZero_4115_; 
v_body_4113_ = lean_ctor_get(v_x_4061_, 2);
lean_inc_ref(v_body_4113_);
lean_dec_ref_known(v_x_4061_, 3);
v_zero_4114_ = lean_unsigned_to_nat(0u);
v_isZero_4115_ = lean_nat_dec_eq(v_x_4062_, v_zero_4114_);
if (v_isZero_4115_ == 1)
{
uint8_t v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec_ref(v_body_4113_);
lean_dec(v_x_4062_);
v___x_4116_ = 0;
v___x_4117_ = lean_box(v___x_4116_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
else
{
lean_object* v_one_4119_; lean_object* v_n_4120_; 
v_one_4119_ = lean_unsigned_to_nat(1u);
v_n_4120_ = lean_nat_sub(v_x_4062_, v_one_4119_);
lean_dec(v_x_4062_);
v_x_4061_ = v_body_4113_;
v_x_4062_ = v_n_4120_;
goto _start;
}
}
default: 
{
uint8_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec(v_x_4062_);
lean_dec_ref(v_x_4061_);
v___x_4122_ = 2;
v___x_4123_ = lean_box(v___x_4122_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
return v___x_4124_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4061_ = stack[0].m_obj;
lean_object* v_x_4062_ = stack[1].m_obj;
lean_object* v_a_4063_ = stack[2].m_obj;
lean_object* v_a_4064_ = stack[3].m_obj;
lean_object* v_a_4065_ = stack[4].m_obj;
lean_object* v_a_4066_ = stack[5].m_obj;
lean_object* v_res_4125_;
v_res_4125_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4061_, v_x_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
stack->m_obj
 = v_res_4125_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4126_, lean_object* v_x_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4126_, v_x_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec_ref(v_a_4128_);
return v_res_4133_;
}
}
lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
switch(lean_obj_tag(v_x_4134_))
{
case 1:
{
lean_object* v_fvarId_4140_; lean_object* v___x_4141_; 
v_fvarId_4140_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_fvarId_4140_);
lean_dec_ref_known(v_x_4134_, 1);
v___x_4141_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4140_, v_a_4135_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = lean_unsigned_to_nat(0u);
v___x_4144_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4142_, v___x_4143_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4144_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
v_a_4145_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4141_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4141_);
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
case 2:
{
lean_object* v_mvarId_4153_; lean_object* v___x_4154_; 
v_mvarId_4153_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_mvarId_4153_);
lean_dec_ref_known(v_x_4134_, 1);
v___x_4154_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4153_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___x_4156_ = lean_unsigned_to_nat(0u);
v___x_4157_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4155_, v___x_4156_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4157_;
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
v_a_4158_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4154_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4154_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
case 3:
{
uint8_t v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_dec_ref_known(v_x_4134_, 1);
v___x_4166_ = 0;
v___x_4167_ = lean_box(v___x_4166_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
return v___x_4168_;
}
case 4:
{
lean_object* v_declName_4169_; lean_object* v_us_4170_; lean_object* v___x_4171_; 
v_declName_4169_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_declName_4169_);
v_us_4170_ = lean_ctor_get(v_x_4134_, 1);
lean_inc(v_us_4170_);
lean_dec_ref_known(v_x_4134_, 2);
v___x_4171_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4169_, v_us_4170_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
v___x_4173_ = lean_unsigned_to_nat(0u);
v___x_4174_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4172_, v___x_4173_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4174_;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4175_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4171_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4171_);
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
case 5:
{
lean_object* v_fn_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v_fn_4183_ = lean_ctor_get(v_x_4134_, 0);
lean_inc_ref(v_fn_4183_);
lean_dec_ref_known(v_x_4134_, 2);
v___x_4184_ = lean_unsigned_to_nat(1u);
v___x_4185_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4183_, v___x_4184_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4185_;
}
case 6:
{
uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
lean_dec_ref_known(v_x_4134_, 3);
v___x_4186_ = 0;
v___x_4187_ = lean_box(v___x_4186_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
case 7:
{
lean_object* v_body_4189_; 
v_body_4189_ = lean_ctor_get(v_x_4134_, 2);
lean_inc_ref(v_body_4189_);
lean_dec_ref_known(v_x_4134_, 3);
v_x_4134_ = v_body_4189_;
goto _start;
}
case 8:
{
lean_object* v_body_4191_; 
v_body_4191_ = lean_ctor_get(v_x_4134_, 3);
lean_inc_ref(v_body_4191_);
lean_dec_ref_known(v_x_4134_, 4);
v_x_4134_ = v_body_4191_;
goto _start;
}
case 9:
{
uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_dec_ref_known(v_x_4134_, 1);
v___x_4193_ = 0;
v___x_4194_ = lean_box(v___x_4193_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
case 10:
{
lean_object* v_expr_4196_; 
v_expr_4196_ = lean_ctor_get(v_x_4134_, 1);
lean_inc_ref(v_expr_4196_);
lean_dec_ref_known(v_x_4134_, 2);
v_x_4134_ = v_expr_4196_;
goto _start;
}
default: 
{
uint8_t v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_dec_ref(v_x_4134_);
v___x_4198_ = 2;
v___x_4199_ = lean_box(v___x_4198_);
v___x_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
return v___x_4200_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isPropQuick_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4134_ = stack[0].m_obj;
lean_object* v_a_4135_ = stack[1].m_obj;
lean_object* v_a_4136_ = stack[2].m_obj;
lean_object* v_a_4137_ = stack[3].m_obj;
lean_object* v_a_4138_ = stack[4].m_obj;
lean_object* v_res_4201_;
v_res_4201_ = l_Lean_Meta_isPropQuick(v_x_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
stack->m_obj
 = v_res_4201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_Meta_isPropQuick(v_x_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
lean_dec(v_a_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_a_4204_);
lean_dec_ref(v_a_4203_);
return v_res_4208_;
}
}
lean_object* l_Lean_Meta_isProp(lean_object* v_e_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v___x_4215_; 
lean_inc_ref(v_e_4209_);
v___x_4215_ = l_Lean_Meta_isPropQuick(v_e_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4272_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4218_ = v___x_4215_;
v_isShared_4219_ = v_isSharedCheck_4272_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4215_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4272_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
uint8_t v___x_4220_; 
v___x_4220_ = lean_unbox(v_a_4216_);
lean_dec(v_a_4216_);
switch(v___x_4220_)
{
case 0:
{
uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4224_; 
lean_dec_ref(v_e_4209_);
v___x_4221_ = 0;
v___x_4222_ = lean_box(v___x_4221_);
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 0, v___x_4222_);
v___x_4224_ = v___x_4218_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
case 1:
{
uint8_t v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
lean_dec_ref(v_e_4209_);
v___x_4226_ = 1;
v___x_4227_ = lean_box(v___x_4226_);
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 0, v___x_4227_);
v___x_4229_ = v___x_4218_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
default: 
{
lean_object* v___x_4231_; 
lean_del_object(v___x_4218_);
lean_inc(v_a_4213_);
lean_inc_ref(v_a_4212_);
lean_inc(v_a_4211_);
lean_inc_ref(v_a_4210_);
v___x_4231_ = lean_infer_type(v_e_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4233_ = l_Lean_Meta_whnfD(v_a_4232_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4255_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4236_ = v___x_4233_;
v_isShared_4237_ = v_isSharedCheck_4255_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4233_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4255_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
if (lean_obj_tag(v_a_4234_) == 3)
{
lean_object* v_u_4238_; lean_object* v___x_4239_; lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4249_; 
lean_del_object(v___x_4236_);
v_u_4238_ = lean_ctor_get(v_a_4234_, 0);
lean_inc(v_u_4238_);
lean_dec_ref_known(v_a_4234_, 1);
v___x_4239_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4238_, v_a_4211_);
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4242_ = v___x_4239_;
v_isShared_4243_ = v_isSharedCheck_4249_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4239_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4249_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
uint8_t v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
v___x_4244_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4240_);
lean_dec(v_a_4240_);
v___x_4245_ = lean_box(v___x_4244_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4245_);
v___x_4247_ = v___x_4242_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
else
{
uint8_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4253_; 
lean_dec(v_a_4234_);
v___x_4250_ = 0;
v___x_4251_ = lean_box(v___x_4250_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 0, v___x_4251_);
v___x_4253_ = v___x_4236_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
v_a_4256_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4233_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4233_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
v_a_4264_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4231_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4231_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec_ref(v_e_4209_);
v_a_4273_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4215_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4215_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isProp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4209_ = stack[0].m_obj;
lean_object* v_a_4210_ = stack[1].m_obj;
lean_object* v_a_4211_ = stack[2].m_obj;
lean_object* v_a_4212_ = stack[3].m_obj;
lean_object* v_a_4213_ = stack[4].m_obj;
lean_object* v_res_4281_;
v_res_4281_ = l_Lean_Meta_isProp(v_e_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
stack->m_obj
 = v_res_4281_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lean_Meta_isProp(v_e_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4289_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = lean_obj_tag_nat(v_x_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4291_);
lean_dec(v_x_4291_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4293_, lean_object* v_k_4294_){
_start:
{
if (lean_obj_tag(v_t_4293_) == 3)
{
lean_object* v_idx_4295_; lean_object* v_numArgs_4296_; lean_object* v___x_4297_; 
v_idx_4295_ = lean_ctor_get(v_t_4293_, 0);
lean_inc(v_idx_4295_);
v_numArgs_4296_ = lean_ctor_get(v_t_4293_, 1);
lean_inc(v_numArgs_4296_);
lean_dec_ref_known(v_t_4293_, 2);
v___x_4297_ = lean_apply_2(v_k_4294_, v_idx_4295_, v_numArgs_4296_);
return v___x_4297_;
}
else
{
lean_dec(v_t_4293_);
return v_k_4294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4298_, lean_object* v_ctorIdx_4299_, lean_object* v_t_4300_, lean_object* v_h_4301_, lean_object* v_k_4302_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4300_, v_k_4302_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4304_, lean_object* v_ctorIdx_4305_, lean_object* v_t_4306_, lean_object* v_h_4307_, lean_object* v_k_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4304_, v_ctorIdx_4305_, v_t_4306_, v_h_4307_, v_k_4308_);
lean_dec(v_ctorIdx_4305_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4310_, lean_object* v_false_4311_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4310_, v_false_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4313_, lean_object* v_t_4314_, lean_object* v_h_4315_, lean_object* v_false_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4314_, v_false_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4318_, lean_object* v_true_4319_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4318_, v_true_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4321_, lean_object* v_t_4322_, lean_object* v_h_4323_, lean_object* v_true_4324_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4322_, v_true_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4326_, lean_object* v_undef_4327_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4326_, v_undef_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4329_, lean_object* v_t_4330_, lean_object* v_h_4331_, lean_object* v_undef_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4330_, v_undef_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4334_, lean_object* v_bvar_4335_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4334_, v_bvar_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4337_, lean_object* v_t_4338_, lean_object* v_h_4339_, lean_object* v_bvar_4340_){
_start:
{
lean_object* v___x_4341_; 
v___x_4341_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4338_, v_bvar_4340_);
return v___x_4341_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4342_){
_start:
{
switch(v_x_4342_)
{
case 0:
{
lean_object* v___x_4343_; 
v___x_4343_ = lean_box(0);
return v___x_4343_;
}
case 1:
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_box(1);
return v___x_4344_;
}
default: 
{
lean_object* v___x_4345_; 
v___x_4345_ = lean_box(2);
return v___x_4345_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4342_ = stack[0].m_num;
lean_object* v_res_4346_;
v_res_4346_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_4342_);
stack->m_obj
 = v_res_4346_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4347_){
_start:
{
uint8_t v_x_25__boxed_4348_; lean_object* v_res_4349_; 
v_x_25__boxed_4348_ = lean_unbox(v_x_4347_);
v_res_4349_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4348_);
return v_res_4349_;
}
}
uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4350_){
_start:
{
switch(lean_obj_tag(v_x_4350_))
{
case 0:
{
uint8_t v___x_4351_; 
v___x_4351_ = 0;
return v___x_4351_;
}
case 1:
{
uint8_t v___x_4352_; 
v___x_4352_ = 1;
return v___x_4352_;
}
default: 
{
uint8_t v___x_4353_; 
v___x_4353_ = 2;
return v___x_4353_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4350_ = stack[0].m_obj;
uint8_t v_res_4354_;
v_res_4354_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4350_);
stack->m_num = v_res_4354_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4355_){
_start:
{
uint8_t v_res_4356_; lean_object* v_r_4357_; 
v_res_4356_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4355_);
lean_dec(v_x_4355_);
v_r_4357_ = lean_box(v_res_4356_);
return v_r_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4359_, lean_object* v_numArgs_4360_){
_start:
{
switch(lean_obj_tag(v_e_4359_))
{
case 3:
{
lean_object* v_u_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v_u_4361_ = lean_ctor_get(v_e_4359_, 0);
v___x_4362_ = lean_unsigned_to_nat(0u);
v___x_4363_ = lean_nat_dec_eq(v_numArgs_4360_, v___x_4362_);
lean_dec(v_numArgs_4360_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_box(2);
return v___x_4364_;
}
else
{
uint8_t v___x_4365_; 
v___x_4365_ = l_Lean_Level_isNeverZero(v_u_4361_);
if (v___x_4365_ == 0)
{
uint8_t v___x_4366_; 
v___x_4366_ = l_Lean_Level_isZero(v_u_4361_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; 
v___x_4367_ = lean_box(2);
return v___x_4367_;
}
else
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_box(1);
return v___x_4368_;
}
}
else
{
lean_object* v___x_4369_; 
v___x_4369_ = lean_box(0);
return v___x_4369_;
}
}
}
case 7:
{
lean_object* v_body_4370_; lean_object* v_zero_4371_; uint8_t v_isZero_4372_; 
v_body_4370_ = lean_ctor_get(v_e_4359_, 2);
v_zero_4371_ = lean_unsigned_to_nat(0u);
v_isZero_4372_ = lean_nat_dec_eq(v_numArgs_4360_, v_zero_4371_);
if (v_isZero_4372_ == 0)
{
lean_object* v_one_4373_; lean_object* v_n_4374_; 
v_one_4373_ = lean_unsigned_to_nat(1u);
v_n_4374_ = lean_nat_sub(v_numArgs_4360_, v_one_4373_);
lean_dec(v_numArgs_4360_);
v_e_4359_ = v_body_4370_;
v_numArgs_4360_ = v_n_4374_;
goto _start;
}
else
{
lean_object* v___x_4376_; 
lean_dec(v_numArgs_4360_);
v___x_4376_ = lean_box(2);
return v___x_4376_;
}
}
case 10:
{
lean_object* v_expr_4377_; 
v_expr_4377_ = lean_ctor_get(v_e_4359_, 1);
v_e_4359_ = v_expr_4377_;
goto _start;
}
case 5:
{
lean_object* v_fn_4379_; 
v_fn_4379_ = lean_ctor_get(v_e_4359_, 0);
if (lean_obj_tag(v_fn_4379_) == 4)
{
lean_object* v_declName_4380_; 
v_declName_4380_ = lean_ctor_get(v_fn_4379_, 0);
if (lean_obj_tag(v_declName_4380_) == 1)
{
lean_object* v_pre_4381_; 
v_pre_4381_ = lean_ctor_get(v_declName_4380_, 0);
if (lean_obj_tag(v_pre_4381_) == 0)
{
lean_object* v_arg_4382_; lean_object* v_str_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; 
v_arg_4382_ = lean_ctor_get(v_e_4359_, 1);
v_str_4383_ = lean_ctor_get(v_declName_4380_, 1);
v___x_4384_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4385_ = lean_string_dec_eq(v_str_4383_, v___x_4384_);
if (v___x_4385_ == 0)
{
lean_object* v___x_4386_; 
lean_dec(v_numArgs_4360_);
v___x_4386_ = lean_box(2);
return v___x_4386_;
}
else
{
v_e_4359_ = v_arg_4382_;
goto _start;
}
}
else
{
lean_object* v___x_4388_; 
lean_dec(v_numArgs_4360_);
v___x_4388_ = lean_box(2);
return v___x_4388_;
}
}
else
{
lean_object* v___x_4389_; 
lean_dec(v_numArgs_4360_);
v___x_4389_ = lean_box(2);
return v___x_4389_;
}
}
else
{
lean_object* v___x_4390_; 
lean_dec(v_numArgs_4360_);
v___x_4390_ = lean_box(2);
return v___x_4390_;
}
}
default: 
{
lean_object* v___x_4391_; 
lean_dec(v_numArgs_4360_);
v___x_4391_ = lean_box(2);
return v___x_4391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4392_, lean_object* v_numArgs_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4392_, v_numArgs_4393_);
lean_dec_ref(v_e_4392_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4395_, lean_object* v_binderType_4396_){
_start:
{
if (lean_obj_tag(v_r_4395_) == 3)
{
lean_object* v_idx_4397_; lean_object* v_numArgs_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4410_; 
v_idx_4397_ = lean_ctor_get(v_r_4395_, 0);
v_numArgs_4398_ = lean_ctor_get(v_r_4395_, 1);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_r_4395_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4400_ = v_r_4395_;
v_isShared_4401_ = v_isSharedCheck_4410_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_numArgs_4398_);
lean_inc(v_idx_4397_);
lean_dec(v_r_4395_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4410_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v_zero_4402_; uint8_t v_isZero_4403_; 
v_zero_4402_ = lean_unsigned_to_nat(0u);
v_isZero_4403_ = lean_nat_dec_eq(v_idx_4397_, v_zero_4402_);
if (v_isZero_4403_ == 1)
{
lean_object* v___x_4404_; 
lean_del_object(v___x_4400_);
lean_dec(v_idx_4397_);
v___x_4404_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4396_, v_numArgs_4398_);
return v___x_4404_;
}
else
{
lean_object* v_one_4405_; lean_object* v_n_4406_; lean_object* v___x_4408_; 
v_one_4405_ = lean_unsigned_to_nat(1u);
v_n_4406_ = lean_nat_sub(v_idx_4397_, v_one_4405_);
lean_dec(v_idx_4397_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 0, v_n_4406_);
v___x_4408_ = v___x_4400_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_n_4406_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_numArgs_4398_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
else
{
return v_r_4395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4411_, lean_object* v_binderType_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4411_, v_binderType_4412_);
lean_dec_ref(v_binderType_4412_);
return v_res_4413_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4414_, lean_object* v_x_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
lean_object* v_type_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; 
switch(lean_obj_tag(v_x_4414_))
{
case 7:
{
lean_object* v_binderType_4454_; lean_object* v_body_4455_; lean_object* v_zero_4456_; uint8_t v_isZero_4457_; 
v_binderType_4454_ = lean_ctor_get(v_x_4414_, 1);
v_body_4455_ = lean_ctor_get(v_x_4414_, 2);
v_zero_4456_ = lean_unsigned_to_nat(0u);
v_isZero_4457_ = lean_nat_dec_eq(v_x_4415_, v_zero_4456_);
if (v_isZero_4457_ == 1)
{
v_type_4422_ = v_x_4414_;
v___y_4423_ = v_a_4416_;
v___y_4424_ = v_a_4417_;
v___y_4425_ = v_a_4418_;
v___y_4426_ = v_a_4419_;
goto v___jp_4421_;
}
else
{
lean_object* v_one_4458_; lean_object* v_n_4459_; lean_object* v___x_4460_; 
lean_inc_ref(v_body_4455_);
lean_inc_ref(v_binderType_4454_);
lean_dec_ref_known(v_x_4414_, 3);
v_one_4458_ = lean_unsigned_to_nat(1u);
v_n_4459_ = lean_nat_sub(v_x_4415_, v_one_4458_);
v___x_4460_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4455_, v_n_4459_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
lean_dec(v_n_4459_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4469_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4463_ = v___x_4460_;
v_isShared_4464_ = v_isSharedCheck_4469_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4460_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4469_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4465_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4461_, v_binderType_4454_);
lean_dec_ref(v_binderType_4454_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4465_);
v___x_4467_ = v___x_4463_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
else
{
lean_dec_ref(v_binderType_4454_);
return v___x_4460_;
}
}
}
case 8:
{
lean_object* v_type_4470_; lean_object* v_body_4471_; lean_object* v___x_4472_; 
v_type_4470_ = lean_ctor_get(v_x_4414_, 1);
lean_inc_ref(v_type_4470_);
v_body_4471_ = lean_ctor_get(v_x_4414_, 3);
lean_inc_ref(v_body_4471_);
lean_dec_ref_known(v_x_4414_, 4);
v___x_4472_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4471_, v_x_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4481_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4481_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4481_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4477_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4473_, v_type_4470_);
lean_dec_ref(v_type_4470_);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v___x_4477_);
v___x_4479_ = v___x_4475_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
else
{
lean_dec_ref(v_type_4470_);
return v___x_4472_;
}
}
case 10:
{
lean_object* v_expr_4482_; 
v_expr_4482_ = lean_ctor_get(v_x_4414_, 1);
lean_inc_ref(v_expr_4482_);
lean_dec_ref_known(v_x_4414_, 2);
v_x_4414_ = v_expr_4482_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; 
v_deBruijnIndex_4484_ = lean_ctor_get(v_x_4414_, 0);
lean_inc(v_deBruijnIndex_4484_);
lean_dec_ref_known(v_x_4414_, 1);
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = lean_nat_dec_eq(v_x_4415_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_dec(v_deBruijnIndex_4484_);
goto v___jp_4451_;
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4487_, 0, v_deBruijnIndex_4484_);
lean_ctor_set(v___x_4487_, 1, v___x_4485_);
v___x_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
return v___x_4488_;
}
}
default: 
{
lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4489_ = lean_unsigned_to_nat(0u);
v___x_4490_ = lean_nat_dec_eq(v_x_4415_, v___x_4489_);
if (v___x_4490_ == 0)
{
lean_dec_ref(v_x_4414_);
goto v___jp_4451_;
}
else
{
v_type_4422_ = v_x_4414_;
v___y_4423_ = v_a_4416_;
v___y_4424_ = v_a_4417_;
v___y_4425_ = v_a_4418_;
v___y_4426_ = v_a_4419_;
goto v___jp_4421_;
}
}
}
v___jp_4421_:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_Expr_getAppFn(v_type_4422_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_deBruijnIndex_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_deBruijnIndex_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_deBruijnIndex_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v___x_4429_ = l_Lean_Expr_getAppNumArgs(v_type_4422_);
lean_dec_ref(v_type_4422_);
v___x_4430_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4430_, 0, v_deBruijnIndex_4428_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
return v___x_4431_;
}
else
{
lean_object* v___x_4432_; 
lean_dec_ref(v___x_4427_);
v___x_4432_ = l_Lean_Meta_isPropQuick(v_type_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4442_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4442_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4442_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
uint8_t v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4437_ = lean_unbox(v_a_4433_);
lean_dec(v_a_4433_);
v___x_4438_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4437_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4438_);
v___x_4440_ = v___x_4435_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4438_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
v_a_4443_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4432_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4432_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
}
v___jp_4451_:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = lean_box(2);
v___x_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
return v___x_4453_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4414_ = stack[0].m_obj;
lean_object* v_x_4415_ = stack[1].m_obj;
lean_object* v_a_4416_ = stack[2].m_obj;
lean_object* v_a_4417_ = stack[3].m_obj;
lean_object* v_a_4418_ = stack[4].m_obj;
lean_object* v_a_4419_ = stack[5].m_obj;
lean_object* v_res_4491_;
v_res_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4414_, v_x_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
stack->m_obj
 = v_res_4491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4492_, lean_object* v_x_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4492_, v_x_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
lean_dec(v_x_4493_);
return v_res_4499_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4500_, lean_object* v_n_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4500_, v_n_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4517_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4510_ = v___x_4507_;
v_isShared_4511_ = v_isSharedCheck_4517_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4507_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4517_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
uint8_t v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4515_; 
v___x_4512_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4508_);
lean_dec(v_a_4508_);
v___x_4513_ = lean_box(v___x_4512_);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v___x_4513_);
v___x_4515_ = v___x_4510_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
v_a_4518_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4507_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4507_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4500_ = stack[0].m_obj;
lean_object* v_n_4501_ = stack[1].m_obj;
lean_object* v_a_4502_ = stack[2].m_obj;
lean_object* v_a_4503_ = stack[3].m_obj;
lean_object* v_a_4504_ = stack[4].m_obj;
lean_object* v_a_4505_ = stack[5].m_obj;
lean_object* v_res_4526_;
v_res_4526_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4500_, v_n_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
stack->m_obj
 = v_res_4526_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4527_, lean_object* v_n_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4527_, v_n_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_n_4528_);
return v_res_4534_;
}
}
lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
switch(lean_obj_tag(v_x_4535_))
{
case 1:
{
lean_object* v_fvarId_4541_; lean_object* v___x_4542_; 
v_fvarId_4541_ = lean_ctor_get(v_x_4535_, 0);
lean_inc(v_fvarId_4541_);
lean_dec_ref_known(v_x_4535_, 1);
v___x_4542_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4541_, v_a_4536_, v_a_4538_, v_a_4539_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
lean_dec_ref_known(v___x_4542_, 1);
v___x_4544_ = lean_unsigned_to_nat(0u);
v___x_4545_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4543_, v___x_4544_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
return v___x_4545_;
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
v_a_4546_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4542_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4542_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4554_; lean_object* v___x_4555_; 
v_mvarId_4554_ = lean_ctor_get(v_x_4535_, 0);
lean_inc(v_mvarId_4554_);
lean_dec_ref_known(v_x_4535_, 1);
v___x_4555_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4554_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref_known(v___x_4555_, 1);
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4556_, v___x_4557_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
return v___x_4558_;
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
v_a_4559_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4555_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4555_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
case 3:
{
uint8_t v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
lean_dec_ref_known(v_x_4535_, 1);
v___x_4567_ = 0;
v___x_4568_ = lean_box(v___x_4567_);
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
return v___x_4569_;
}
case 4:
{
lean_object* v_declName_4570_; lean_object* v_us_4571_; lean_object* v___x_4572_; 
v_declName_4570_ = lean_ctor_get(v_x_4535_, 0);
lean_inc(v_declName_4570_);
v_us_4571_ = lean_ctor_get(v_x_4535_, 1);
lean_inc(v_us_4571_);
lean_dec_ref_known(v_x_4535_, 2);
v___x_4572_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4570_, v_us_4571_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4573_, v___x_4574_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
return v___x_4575_;
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
v_a_4576_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4572_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4572_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
case 5:
{
lean_object* v_fn_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v_fn_4584_ = lean_ctor_get(v_x_4535_, 0);
lean_inc_ref(v_fn_4584_);
lean_dec_ref_known(v_x_4535_, 2);
v___x_4585_ = lean_unsigned_to_nat(1u);
v___x_4586_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4584_, v___x_4585_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
return v___x_4586_;
}
case 6:
{
lean_object* v_body_4587_; 
v_body_4587_ = lean_ctor_get(v_x_4535_, 2);
lean_inc_ref(v_body_4587_);
lean_dec_ref_known(v_x_4535_, 3);
v_x_4535_ = v_body_4587_;
goto _start;
}
case 7:
{
uint8_t v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
lean_dec_ref_known(v_x_4535_, 3);
v___x_4589_ = 0;
v___x_4590_ = lean_box(v___x_4589_);
v___x_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
return v___x_4591_;
}
case 8:
{
lean_object* v_body_4592_; 
v_body_4592_ = lean_ctor_get(v_x_4535_, 3);
lean_inc_ref(v_body_4592_);
lean_dec_ref_known(v_x_4535_, 4);
v_x_4535_ = v_body_4592_;
goto _start;
}
case 9:
{
uint8_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
lean_dec_ref_known(v_x_4535_, 1);
v___x_4594_ = 0;
v___x_4595_ = lean_box(v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
case 10:
{
lean_object* v_expr_4597_; 
v_expr_4597_ = lean_ctor_get(v_x_4535_, 1);
lean_inc_ref(v_expr_4597_);
lean_dec_ref_known(v_x_4535_, 2);
v_x_4535_ = v_expr_4597_;
goto _start;
}
default: 
{
uint8_t v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
lean_dec_ref(v_x_4535_);
v___x_4599_ = 2;
v___x_4600_ = lean_box(v___x_4599_);
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
return v___x_4601_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isProofQuick_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4535_ = stack[0].m_obj;
lean_object* v_a_4536_ = stack[1].m_obj;
lean_object* v_a_4537_ = stack[2].m_obj;
lean_object* v_a_4538_ = stack[3].m_obj;
lean_object* v_a_4539_ = stack[4].m_obj;
lean_object* v_res_4602_;
v_res_4602_ = l_Lean_Meta_isProofQuick(v_x_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
stack->m_obj
 = v_res_4602_;
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4603_, lean_object* v_x_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_){
_start:
{
switch(lean_obj_tag(v_x_4603_))
{
case 4:
{
lean_object* v_declName_4610_; lean_object* v_us_4611_; lean_object* v___x_4612_; 
v_declName_4610_ = lean_ctor_get(v_x_4603_, 0);
lean_inc(v_declName_4610_);
v_us_4611_ = lean_ctor_get(v_x_4603_, 1);
lean_inc(v_us_4611_);
lean_dec_ref_known(v_x_4603_, 2);
v___x_4612_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4610_, v_us_4611_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4614_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc(v_a_4613_);
lean_dec_ref_known(v___x_4612_, 1);
v___x_4614_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4613_, v_x_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
lean_dec(v_x_4604_);
return v___x_4614_;
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec(v_x_4604_);
v_a_4615_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4612_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4612_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4623_; lean_object* v___x_4624_; 
v_fvarId_4623_ = lean_ctor_get(v_x_4603_, 0);
lean_inc(v_fvarId_4623_);
lean_dec_ref_known(v_x_4603_, 1);
v___x_4624_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4623_, v_a_4605_, v_a_4607_, v_a_4608_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4626_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4625_, v_x_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
lean_dec(v_x_4604_);
return v___x_4626_;
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_dec(v_x_4604_);
v_a_4627_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4624_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4624_);
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
case 2:
{
lean_object* v_mvarId_4635_; lean_object* v___x_4636_; 
v_mvarId_4635_ = lean_ctor_get(v_x_4603_, 0);
lean_inc(v_mvarId_4635_);
lean_dec_ref_known(v_x_4603_, 1);
v___x_4636_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4635_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4638_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4636_, 1);
v___x_4638_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4637_, v_x_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
lean_dec(v_x_4604_);
return v___x_4638_;
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec(v_x_4604_);
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
case 5:
{
lean_object* v_fn_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_fn_4647_ = lean_ctor_get(v_x_4603_, 0);
lean_inc_ref(v_fn_4647_);
lean_dec_ref_known(v_x_4603_, 2);
v___x_4648_ = lean_unsigned_to_nat(1u);
v___x_4649_ = lean_nat_add(v_x_4604_, v___x_4648_);
lean_dec(v_x_4604_);
v_x_4603_ = v_fn_4647_;
v_x_4604_ = v___x_4649_;
goto _start;
}
case 10:
{
lean_object* v_expr_4651_; 
v_expr_4651_ = lean_ctor_get(v_x_4603_, 1);
lean_inc_ref(v_expr_4651_);
lean_dec_ref_known(v_x_4603_, 2);
v_x_4603_ = v_expr_4651_;
goto _start;
}
case 8:
{
lean_object* v_body_4653_; 
v_body_4653_ = lean_ctor_get(v_x_4603_, 3);
lean_inc_ref(v_body_4653_);
lean_dec_ref_known(v_x_4603_, 4);
v_x_4603_ = v_body_4653_;
goto _start;
}
case 6:
{
lean_object* v_body_4655_; lean_object* v_zero_4656_; uint8_t v_isZero_4657_; 
v_body_4655_ = lean_ctor_get(v_x_4603_, 2);
lean_inc_ref(v_body_4655_);
lean_dec_ref_known(v_x_4603_, 3);
v_zero_4656_ = lean_unsigned_to_nat(0u);
v_isZero_4657_ = lean_nat_dec_eq(v_x_4604_, v_zero_4656_);
if (v_isZero_4657_ == 1)
{
lean_object* v___x_4658_; 
lean_dec(v_x_4604_);
v___x_4658_ = l_Lean_Meta_isProofQuick(v_body_4655_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
return v___x_4658_;
}
else
{
lean_object* v_one_4659_; lean_object* v_n_4660_; 
v_one_4659_ = lean_unsigned_to_nat(1u);
v_n_4660_ = lean_nat_sub(v_x_4604_, v_one_4659_);
lean_dec(v_x_4604_);
v_x_4603_ = v_body_4655_;
v_x_4604_ = v_n_4660_;
goto _start;
}
}
default: 
{
uint8_t v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
lean_dec(v_x_4604_);
lean_dec_ref(v_x_4603_);
v___x_4662_ = 2;
v___x_4663_ = lean_box(v___x_4662_);
v___x_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
return v___x_4664_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4603_ = stack[0].m_obj;
lean_object* v_x_4604_ = stack[1].m_obj;
lean_object* v_a_4605_ = stack[2].m_obj;
lean_object* v_a_4606_ = stack[3].m_obj;
lean_object* v_a_4607_ = stack[4].m_obj;
lean_object* v_a_4608_ = stack[5].m_obj;
lean_object* v_res_4665_;
v_res_4665_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4603_, v_x_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
stack->m_obj
 = v_res_4665_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4666_, lean_object* v_x_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4666_, v_x_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
lean_dec(v_a_4669_);
lean_dec_ref(v_a_4668_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l_Lean_Meta_isProofQuick(v_x_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
return v_res_4680_;
}
}
lean_object* l_Lean_Meta_isProof(lean_object* v_e_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v___x_4687_; 
lean_inc_ref(v_e_4681_);
v___x_4687_ = l_Lean_Meta_isProofQuick(v_e_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4714_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4690_ = v___x_4687_;
v_isShared_4691_ = v_isSharedCheck_4714_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4687_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4714_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
uint8_t v___x_4692_; 
v___x_4692_ = lean_unbox(v_a_4688_);
lean_dec(v_a_4688_);
switch(v___x_4692_)
{
case 0:
{
uint8_t v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4696_; 
lean_dec_ref(v_e_4681_);
v___x_4693_ = 0;
v___x_4694_ = lean_box(v___x_4693_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 0, v___x_4694_);
v___x_4696_ = v___x_4690_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4694_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
case 1:
{
uint8_t v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4701_; 
lean_dec_ref(v_e_4681_);
v___x_4698_ = 1;
v___x_4699_ = lean_box(v___x_4698_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 0, v___x_4699_);
v___x_4701_ = v___x_4690_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4699_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
default: 
{
lean_object* v___x_4703_; 
lean_del_object(v___x_4690_);
lean_inc(v_a_4685_);
lean_inc_ref(v_a_4684_);
lean_inc(v_a_4683_);
lean_inc_ref(v_a_4682_);
v___x_4703_ = lean_infer_type(v_e_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4705_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
lean_inc(v_a_4704_);
lean_dec_ref_known(v___x_4703_, 1);
v___x_4705_ = l_Lean_Meta_isProp(v_a_4704_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
return v___x_4705_;
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
v_a_4706_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___x_4703_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4703_);
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
}
}
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4722_; 
lean_dec_ref(v_e_4681_);
v_a_4715_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4717_ = v___x_4687_;
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4687_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4681_ = stack[0].m_obj;
lean_object* v_a_4682_ = stack[1].m_obj;
lean_object* v_a_4683_ = stack[2].m_obj;
lean_object* v_a_4684_ = stack[3].m_obj;
lean_object* v_a_4685_ = stack[4].m_obj;
lean_object* v_res_4723_;
v_res_4723_ = l_Lean_Meta_isProof(v_e_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
stack->m_obj
 = v_res_4723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Lean_Meta_isProof(v_e_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_);
lean_dec(v_a_4728_);
lean_dec_ref(v_a_4727_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
return v_res_4730_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4731_, lean_object* v_x_4732_){
_start:
{
switch(lean_obj_tag(v_x_4731_))
{
case 3:
{
lean_object* v___x_4738_; uint8_t v___x_4739_; 
v___x_4738_ = lean_unsigned_to_nat(0u);
v___x_4739_ = lean_nat_dec_eq(v_x_4732_, v___x_4738_);
lean_dec(v_x_4732_);
if (v___x_4739_ == 0)
{
goto v___jp_4734_;
}
else
{
uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = 1;
v___x_4741_ = lean_box(v___x_4740_);
v___x_4742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
return v___x_4742_;
}
}
case 7:
{
lean_object* v_body_4743_; lean_object* v_zero_4744_; uint8_t v_isZero_4745_; 
v_body_4743_ = lean_ctor_get(v_x_4731_, 2);
v_zero_4744_ = lean_unsigned_to_nat(0u);
v_isZero_4745_ = lean_nat_dec_eq(v_x_4732_, v_zero_4744_);
if (v_isZero_4745_ == 1)
{
uint8_t v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
lean_dec(v_x_4732_);
v___x_4746_ = 0;
v___x_4747_ = lean_box(v___x_4746_);
v___x_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4747_);
return v___x_4748_;
}
else
{
lean_object* v_one_4749_; lean_object* v_n_4750_; 
v_one_4749_ = lean_unsigned_to_nat(1u);
v_n_4750_ = lean_nat_sub(v_x_4732_, v_one_4749_);
lean_dec(v_x_4732_);
v_x_4731_ = v_body_4743_;
v_x_4732_ = v_n_4750_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4752_; 
v_body_4752_ = lean_ctor_get(v_x_4731_, 3);
v_x_4731_ = v_body_4752_;
goto _start;
}
case 10:
{
lean_object* v_expr_4754_; 
v_expr_4754_ = lean_ctor_get(v_x_4731_, 1);
v_x_4731_ = v_expr_4754_;
goto _start;
}
default: 
{
lean_dec(v_x_4732_);
goto v___jp_4734_;
}
}
v___jp_4734_:
{
uint8_t v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4735_ = 2;
v___x_4736_ = lean_box(v___x_4735_);
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
return v___x_4737_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4731_ = stack[0].m_obj;
lean_object* v_x_4732_ = stack[1].m_obj;
lean_object* v_res_4756_;
v_res_4756_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4731_, v_x_4732_);
stack->m_obj
 = v_res_4756_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4757_, lean_object* v_x_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4757_, v_x_4758_);
lean_dec_ref(v_x_4757_);
return v_res_4760_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4761_, lean_object* v_x_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v___x_4768_; 
v___x_4768_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4761_, v_x_4762_);
return v___x_4768_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4761_ = stack[0].m_obj;
lean_object* v_x_4762_ = stack[1].m_obj;
lean_object* v_a_4763_ = stack[2].m_obj;
lean_object* v_a_4764_ = stack[3].m_obj;
lean_object* v_a_4765_ = stack[4].m_obj;
lean_object* v_a_4766_ = stack[5].m_obj;
lean_object* v_res_4769_;
v_res_4769_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4761_, v_x_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
stack->m_obj
 = v_res_4769_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4770_, lean_object* v_x_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4770_, v_x_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec_ref(v_x_4770_);
return v_res_4777_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4778_, lean_object* v_x_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
switch(lean_obj_tag(v_x_4778_))
{
case 4:
{
lean_object* v_declName_4785_; lean_object* v_us_4786_; lean_object* v___x_4787_; 
v_declName_4785_ = lean_ctor_get(v_x_4778_, 0);
lean_inc(v_declName_4785_);
v_us_4786_ = lean_ctor_get(v_x_4778_, 1);
lean_inc(v_us_4786_);
lean_dec_ref_known(v_x_4778_, 2);
v___x_4787_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4785_, v_us_4786_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4789_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v___x_4787_, 1);
v___x_4789_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4788_, v_x_4779_);
lean_dec(v_a_4788_);
return v___x_4789_;
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v_x_4779_);
v_a_4790_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4787_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4787_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4798_; lean_object* v___x_4799_; 
v_fvarId_4798_ = lean_ctor_get(v_x_4778_, 0);
lean_inc(v_fvarId_4798_);
lean_dec_ref_known(v_x_4778_, 1);
v___x_4799_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4798_, v_a_4780_, v_a_4782_, v_a_4783_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4801_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
lean_inc(v_a_4800_);
lean_dec_ref_known(v___x_4799_, 1);
v___x_4801_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4800_, v_x_4779_);
lean_dec(v_a_4800_);
return v___x_4801_;
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
lean_dec(v_x_4779_);
v_a_4802_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4799_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4799_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
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
case 2:
{
lean_object* v_mvarId_4810_; lean_object* v___x_4811_; 
v_mvarId_4810_ = lean_ctor_get(v_x_4778_, 0);
lean_inc(v_mvarId_4810_);
lean_dec_ref_known(v_x_4778_, 1);
v___x_4811_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4810_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v_a_4812_; lean_object* v___x_4813_; 
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_a_4812_);
lean_dec_ref_known(v___x_4811_, 1);
v___x_4813_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4812_, v_x_4779_);
lean_dec(v_a_4812_);
return v___x_4813_;
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
lean_dec(v_x_4779_);
v_a_4814_ = lean_ctor_get(v___x_4811_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4811_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4811_);
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
case 5:
{
lean_object* v_fn_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v_fn_4822_ = lean_ctor_get(v_x_4778_, 0);
lean_inc_ref(v_fn_4822_);
lean_dec_ref_known(v_x_4778_, 2);
v___x_4823_ = lean_unsigned_to_nat(1u);
v___x_4824_ = lean_nat_add(v_x_4779_, v___x_4823_);
lean_dec(v_x_4779_);
v_x_4778_ = v_fn_4822_;
v_x_4779_ = v___x_4824_;
goto _start;
}
case 10:
{
lean_object* v_expr_4826_; 
v_expr_4826_ = lean_ctor_get(v_x_4778_, 1);
lean_inc_ref(v_expr_4826_);
lean_dec_ref_known(v_x_4778_, 2);
v_x_4778_ = v_expr_4826_;
goto _start;
}
case 8:
{
lean_object* v_body_4828_; 
v_body_4828_ = lean_ctor_get(v_x_4778_, 3);
lean_inc_ref(v_body_4828_);
lean_dec_ref_known(v_x_4778_, 4);
v_x_4778_ = v_body_4828_;
goto _start;
}
case 6:
{
lean_object* v_body_4830_; lean_object* v_zero_4831_; uint8_t v_isZero_4832_; 
v_body_4830_ = lean_ctor_get(v_x_4778_, 2);
lean_inc_ref(v_body_4830_);
lean_dec_ref_known(v_x_4778_, 3);
v_zero_4831_ = lean_unsigned_to_nat(0u);
v_isZero_4832_ = lean_nat_dec_eq(v_x_4779_, v_zero_4831_);
if (v_isZero_4832_ == 1)
{
uint8_t v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
lean_dec_ref(v_body_4830_);
lean_dec(v_x_4779_);
v___x_4833_ = 0;
v___x_4834_ = lean_box(v___x_4833_);
v___x_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4834_);
return v___x_4835_;
}
else
{
lean_object* v_one_4836_; lean_object* v_n_4837_; 
v_one_4836_ = lean_unsigned_to_nat(1u);
v_n_4837_ = lean_nat_sub(v_x_4779_, v_one_4836_);
lean_dec(v_x_4779_);
v_x_4778_ = v_body_4830_;
v_x_4779_ = v_n_4837_;
goto _start;
}
}
default: 
{
uint8_t v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
lean_dec(v_x_4779_);
lean_dec_ref(v_x_4778_);
v___x_4839_ = 2;
v___x_4840_ = lean_box(v___x_4839_);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4778_ = stack[0].m_obj;
lean_object* v_x_4779_ = stack[1].m_obj;
lean_object* v_a_4780_ = stack[2].m_obj;
lean_object* v_a_4781_ = stack[3].m_obj;
lean_object* v_a_4782_ = stack[4].m_obj;
lean_object* v_a_4783_ = stack[5].m_obj;
lean_object* v_res_4842_;
v_res_4842_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4778_, v_x_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
stack->m_obj
 = v_res_4842_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4843_, lean_object* v_x_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4843_, v_x_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
return v_res_4850_;
}
}
lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
switch(lean_obj_tag(v_x_4851_))
{
case 1:
{
lean_object* v_fvarId_4857_; lean_object* v___x_4858_; 
v_fvarId_4857_ = lean_ctor_get(v_x_4851_, 0);
lean_inc(v_fvarId_4857_);
lean_dec_ref_known(v_x_4851_, 1);
v___x_4858_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4857_, v_a_4852_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4858_, 1);
v___x_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4859_, v___x_4860_);
lean_dec(v_a_4859_);
return v___x_4861_;
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
v_a_4862_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4858_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4858_);
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
case 2:
{
lean_object* v_mvarId_4870_; lean_object* v___x_4871_; 
v_mvarId_4870_ = lean_ctor_get(v_x_4851_, 0);
lean_inc(v_mvarId_4870_);
lean_dec_ref_known(v_x_4851_, 1);
v___x_4871_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4870_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4872_);
lean_dec_ref_known(v___x_4871_, 1);
v___x_4873_ = lean_unsigned_to_nat(0u);
v___x_4874_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4872_, v___x_4873_);
lean_dec(v_a_4872_);
return v___x_4874_;
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
v_a_4875_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4877_ = v___x_4871_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4871_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
}
case 3:
{
uint8_t v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
lean_dec_ref_known(v_x_4851_, 1);
v___x_4883_ = 1;
v___x_4884_ = lean_box(v___x_4883_);
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4884_);
return v___x_4885_;
}
case 4:
{
lean_object* v_declName_4886_; lean_object* v_us_4887_; lean_object* v___x_4888_; 
v_declName_4886_ = lean_ctor_get(v_x_4851_, 0);
lean_inc(v_declName_4886_);
v_us_4887_ = lean_ctor_get(v_x_4851_, 1);
lean_inc(v_us_4887_);
lean_dec_ref_known(v_x_4851_, 2);
v___x_4888_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4886_, v_us_4887_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref_known(v___x_4888_, 1);
v___x_4890_ = lean_unsigned_to_nat(0u);
v___x_4891_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4889_, v___x_4890_);
lean_dec(v_a_4889_);
return v___x_4891_;
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
v_a_4892_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4888_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4888_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
case 5:
{
lean_object* v_fn_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v_fn_4900_ = lean_ctor_get(v_x_4851_, 0);
lean_inc_ref(v_fn_4900_);
lean_dec_ref_known(v_x_4851_, 2);
v___x_4901_ = lean_unsigned_to_nat(1u);
v___x_4902_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4900_, v___x_4901_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
return v___x_4902_;
}
case 6:
{
uint8_t v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
lean_dec_ref_known(v_x_4851_, 3);
v___x_4903_ = 0;
v___x_4904_ = lean_box(v___x_4903_);
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
return v___x_4905_;
}
case 7:
{
uint8_t v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
lean_dec_ref_known(v_x_4851_, 3);
v___x_4906_ = 1;
v___x_4907_ = lean_box(v___x_4906_);
v___x_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
return v___x_4908_;
}
case 8:
{
lean_object* v_body_4909_; 
v_body_4909_ = lean_ctor_get(v_x_4851_, 3);
lean_inc_ref(v_body_4909_);
lean_dec_ref_known(v_x_4851_, 4);
v_x_4851_ = v_body_4909_;
goto _start;
}
case 9:
{
uint8_t v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
lean_dec_ref_known(v_x_4851_, 1);
v___x_4911_ = 0;
v___x_4912_ = lean_box(v___x_4911_);
v___x_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
return v___x_4913_;
}
case 10:
{
lean_object* v_expr_4914_; 
v_expr_4914_ = lean_ctor_get(v_x_4851_, 1);
lean_inc_ref(v_expr_4914_);
lean_dec_ref_known(v_x_4851_, 2);
v_x_4851_ = v_expr_4914_;
goto _start;
}
default: 
{
uint8_t v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
lean_dec_ref(v_x_4851_);
v___x_4916_ = 2;
v___x_4917_ = lean_box(v___x_4916_);
v___x_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
return v___x_4918_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isTypeQuick_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4851_ = stack[0].m_obj;
lean_object* v_a_4852_ = stack[1].m_obj;
lean_object* v_a_4853_ = stack[2].m_obj;
lean_object* v_a_4854_ = stack[3].m_obj;
lean_object* v_a_4855_ = stack[4].m_obj;
lean_object* v_res_4919_;
v_res_4919_ = l_Lean_Meta_isTypeQuick(v_x_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
stack->m_obj
 = v_res_4919_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_Meta_isTypeQuick(v_x_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec_ref(v_a_4921_);
return v_res_4926_;
}
}
lean_object* l_Lean_Meta_isType(lean_object* v_e_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v___x_4933_; 
lean_inc_ref(v_e_4927_);
v___x_4933_ = l_Lean_Meta_isTypeQuick(v_e_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4983_; 
v_a_4934_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4936_ = v___x_4933_;
v_isShared_4937_ = v_isSharedCheck_4983_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4933_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4983_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
uint8_t v___x_4938_; 
v___x_4938_ = lean_unbox(v_a_4934_);
lean_dec(v_a_4934_);
switch(v___x_4938_)
{
case 0:
{
uint8_t v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
lean_dec_ref(v_e_4927_);
v___x_4939_ = 0;
v___x_4940_ = lean_box(v___x_4939_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v___x_4940_);
v___x_4942_ = v___x_4936_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
case 1:
{
uint8_t v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4947_; 
lean_dec_ref(v_e_4927_);
v___x_4944_ = 1;
v___x_4945_ = lean_box(v___x_4944_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v___x_4945_);
v___x_4947_ = v___x_4936_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
default: 
{
lean_object* v___x_4949_; 
lean_del_object(v___x_4936_);
lean_inc(v_a_4931_);
lean_inc_ref(v_a_4930_);
lean_inc(v_a_4929_);
lean_inc_ref(v_a_4928_);
v___x_4949_ = lean_infer_type(v_e_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4951_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___x_4949_, 1);
v___x_4951_ = l_Lean_Meta_whnfD(v_a_4950_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4966_; 
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4954_ = v___x_4951_;
v_isShared_4955_ = v_isSharedCheck_4966_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4951_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4966_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
if (lean_obj_tag(v_a_4952_) == 3)
{
uint8_t v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4959_; 
lean_dec_ref_known(v_a_4952_, 1);
v___x_4956_ = 1;
v___x_4957_ = lean_box(v___x_4956_);
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 0, v___x_4957_);
v___x_4959_ = v___x_4954_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
else
{
uint8_t v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4964_; 
lean_dec(v_a_4952_);
v___x_4961_ = 0;
v___x_4962_ = lean_box(v___x_4961_);
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 0, v___x_4962_);
v___x_4964_ = v___x_4954_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4962_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
v_a_4967_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4951_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4951_);
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
else
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
v_a_4975_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4949_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4949_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
lean_dec_ref(v_e_4927_);
v_a_4984_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4933_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4933_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4927_ = stack[0].m_obj;
lean_object* v_a_4928_ = stack[1].m_obj;
lean_object* v_a_4929_ = stack[2].m_obj;
lean_object* v_a_4930_ = stack[3].m_obj;
lean_object* v_a_4931_ = stack[4].m_obj;
lean_object* v_res_4992_;
v_res_4992_ = l_Lean_Meta_isType(v_e_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
stack->m_obj
 = v_res_4992_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l_Lean_Meta_isType(v_e_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
return v_res_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_5000_){
_start:
{
switch(lean_obj_tag(v_x_5000_))
{
case 7:
{
lean_object* v_body_5001_; 
v_body_5001_ = lean_ctor_get(v_x_5000_, 2);
v_x_5000_ = v_body_5001_;
goto _start;
}
case 3:
{
lean_object* v_u_5003_; lean_object* v___x_5004_; 
v_u_5003_ = lean_ctor_get(v_x_5000_, 0);
lean_inc(v_u_5003_);
v___x_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5004_, 0, v_u_5003_);
return v___x_5004_;
}
default: 
{
lean_object* v___x_5005_; 
v___x_5005_ = lean_box(0);
return v___x_5005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_5006_);
lean_dec_ref(v_x_5006_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_5008_, lean_object* v_body_5009_, lean_object* v_x_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_5008_, v_body_5009_, v_x_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
lean_dec(v___y_5012_);
lean_dec_ref(v___y_5011_);
return v_res_5016_;
}
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_5019_, lean_object* v_xs_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_){
_start:
{
lean_object* v_l_5027_; 
switch(lean_obj_tag(v_type_5019_))
{
case 3:
{
lean_object* v_u_5030_; 
lean_dec_ref(v_xs_5020_);
v_u_5030_ = lean_ctor_get(v_type_5019_, 0);
lean_inc(v_u_5030_);
lean_dec_ref_known(v_type_5019_, 1);
v_l_5027_ = v_u_5030_;
goto v___jp_5026_;
}
case 7:
{
lean_object* v_binderName_5031_; lean_object* v_binderType_5032_; lean_object* v_body_5033_; uint8_t v_binderInfo_5034_; lean_object* v___f_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v_binderName_5031_ = lean_ctor_get(v_type_5019_, 0);
lean_inc(v_binderName_5031_);
v_binderType_5032_ = lean_ctor_get(v_type_5019_, 1);
lean_inc_ref(v_binderType_5032_);
v_body_5033_ = lean_ctor_get(v_type_5019_, 2);
lean_inc_ref(v_body_5033_);
v_binderInfo_5034_ = lean_ctor_get_uint8(v_type_5019_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_5019_, 3);
lean_inc_ref(v_xs_5020_);
v___f_5035_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5035_, 0, v_xs_5020_);
lean_closure_set(v___f_5035_, 1, v_body_5033_);
v___x_5036_ = lean_expr_instantiate_rev(v_binderType_5032_, v_xs_5020_);
lean_dec_ref(v_xs_5020_);
lean_dec_ref(v_binderType_5032_);
v___x_5037_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_5031_, v_binderInfo_5034_, v___x_5036_, v___f_5035_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
return v___x_5037_;
}
default: 
{
lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5038_ = lean_expr_instantiate_rev(v_type_5019_, v_xs_5020_);
lean_dec_ref(v_xs_5020_);
lean_dec_ref(v_type_5019_);
v___x_5039_ = l_Lean_Meta_whnfD(v___x_5038_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5051_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5051_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5051_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
switch(lean_obj_tag(v_a_5040_))
{
case 3:
{
lean_object* v_u_5044_; 
lean_del_object(v___x_5042_);
v_u_5044_ = lean_ctor_get(v_a_5040_, 0);
lean_inc(v_u_5044_);
lean_dec_ref_known(v_a_5040_, 1);
v_l_5027_ = v_u_5044_;
goto v___jp_5026_;
}
case 7:
{
lean_object* v___x_5045_; 
lean_del_object(v___x_5042_);
v___x_5045_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_5019_ = v_a_5040_;
v_xs_5020_ = v___x_5045_;
goto _start;
}
default: 
{
lean_object* v___x_5047_; lean_object* v___x_5049_; 
lean_dec(v_a_5040_);
v___x_5047_ = lean_box(0);
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5047_);
v___x_5049_ = v___x_5042_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5047_);
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
else
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
v_a_5052_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5054_ = v___x_5039_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5039_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
}
v___jp_5026_:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5028_, 0, v_l_5027_);
v___x_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5028_);
return v___x_5029_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5019_ = stack[0].m_obj;
lean_object* v_xs_5020_ = stack[1].m_obj;
lean_object* v_a_5021_ = stack[2].m_obj;
lean_object* v_a_5022_ = stack[3].m_obj;
lean_object* v_a_5023_ = stack[4].m_obj;
lean_object* v_a_5024_ = stack[5].m_obj;
lean_object* v_res_5060_;
v_res_5060_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5019_, v_xs_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
stack->m_obj
 = v_res_5060_;
}
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_5061_, lean_object* v_body_5062_, lean_object* v_x_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = lean_array_push(v_xs_5061_, v_x_5063_);
v___x_5070_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_5062_, v___x_5069_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
return v___x_5070_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5061_ = stack[0].m_obj;
lean_object* v_body_5062_ = stack[1].m_obj;
lean_object* v_x_5063_ = stack[2].m_obj;
lean_object* v___y_5064_ = stack[3].m_obj;
lean_object* v___y_5065_ = stack[4].m_obj;
lean_object* v___y_5066_ = stack[5].m_obj;
lean_object* v___y_5067_ = stack[6].m_obj;
lean_object* v_res_5071_;
v_res_5071_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_5061_, v_body_5062_, v_x_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
stack->m_obj
 = v_res_5071_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5072_, lean_object* v_xs_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5072_, v_xs_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
lean_dec(v_a_5077_);
lean_dec_ref(v_a_5076_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
return v_res_5079_;
}
}
lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5080_, lean_object* v_cache_5081_, lean_object* v_a_x3f_5082_){
_start:
{
lean_object* v___x_5084_; lean_object* v_mctx_5085_; lean_object* v_zetaDeltaFVarIds_5086_; lean_object* v_postponed_5087_; lean_object* v_diag_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5098_; 
v___x_5084_ = lean_st_ref_take(v_a_5080_);
v_mctx_5085_ = lean_ctor_get(v___x_5084_, 0);
v_zetaDeltaFVarIds_5086_ = lean_ctor_get(v___x_5084_, 2);
v_postponed_5087_ = lean_ctor_get(v___x_5084_, 3);
v_diag_5088_ = lean_ctor_get(v___x_5084_, 4);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5098_ == 0)
{
lean_object* v_unused_5099_; 
v_unused_5099_ = lean_ctor_get(v___x_5084_, 1);
lean_dec(v_unused_5099_);
v___x_5090_ = v___x_5084_;
v_isShared_5091_ = v_isSharedCheck_5098_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_diag_5088_);
lean_inc(v_postponed_5087_);
lean_inc(v_zetaDeltaFVarIds_5086_);
lean_inc(v_mctx_5085_);
lean_dec(v___x_5084_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5098_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; lean_object* v___x_5094_; 
v___x_5092_ = lean_box(0);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 1, v_cache_5081_);
v___x_5094_ = v___x_5090_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_mctx_5085_);
lean_ctor_set(v_reuseFailAlloc_5097_, 1, v_cache_5081_);
lean_ctor_set(v_reuseFailAlloc_5097_, 2, v_zetaDeltaFVarIds_5086_);
lean_ctor_set(v_reuseFailAlloc_5097_, 3, v_postponed_5087_);
lean_ctor_set(v_reuseFailAlloc_5097_, 4, v_diag_5088_);
v___x_5094_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5095_ = lean_st_ref_put(v_a_5080_, v___x_5094_);
v___x_5096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5092_);
return v___x_5096_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_typeFormerTypeLevel___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5080_ = stack[0].m_obj;
lean_object* v_cache_5081_ = stack[1].m_obj;
lean_object* v_a_x3f_5082_ = stack[2].m_obj;
lean_object* v_res_5100_;
v_res_5100_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5080_, v_cache_5081_, v_a_x3f_5082_);
stack->m_obj
 = v_res_5100_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5101_, lean_object* v_cache_5102_, lean_object* v_a_x3f_5103_, lean_object* v___y_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5101_, v_cache_5102_, v_a_x3f_5103_);
lean_dec(v_a_x3f_5103_);
lean_dec(v_a_5101_);
return v_res_5105_;
}
}
lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v___x_5112_; 
v___x_5112_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5106_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v_cache_5115_; lean_object* v___x_5116_; 
v___x_5113_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5114_ = lean_st_ref_get(v_a_5108_);
v_cache_5115_ = lean_ctor_get(v___x_5114_, 1);
lean_inc_ref(v_cache_5115_);
lean_dec(v___x_5114_);
v___x_5116_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5106_, v___x_5113_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5133_; 
v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5119_ = v___x_5116_;
v_isShared_5120_ = v_isSharedCheck_5133_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5116_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5133_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5122_; 
lean_inc(v_a_5117_);
if (v_isShared_5120_ == 0)
{
lean_ctor_set_tag(v___x_5119_, 1);
v___x_5122_ = v___x_5119_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5117_);
v___x_5122_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
lean_object* v___x_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5130_; 
v___x_5123_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5108_, v_cache_5115_, v___x_5122_);
lean_dec_ref(v___x_5122_);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5130_ == 0)
{
lean_object* v_unused_5131_; 
v_unused_5131_ = lean_ctor_get(v___x_5123_, 0);
lean_dec(v_unused_5131_);
v___x_5125_ = v___x_5123_;
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
else
{
lean_dec(v___x_5123_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5130_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v_a_5117_);
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5117_);
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
else
{
lean_object* v_a_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
v_a_5134_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5134_);
lean_dec_ref_known(v___x_5116_, 1);
v___x_5135_ = lean_box(0);
v___x_5136_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5108_, v_cache_5115_, v___x_5135_);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5143_ == 0)
{
lean_object* v_unused_5144_; 
v_unused_5144_ = lean_ctor_get(v___x_5136_, 0);
lean_dec(v_unused_5144_);
v___x_5138_ = v___x_5136_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_dec(v___x_5136_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
lean_ctor_set_tag(v___x_5138_, 1);
lean_ctor_set(v___x_5138_, 0, v_a_5134_);
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5134_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
else
{
lean_object* v___x_5145_; 
lean_dec_ref(v_type_5106_);
v___x_5145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5112_);
return v___x_5145_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_typeFormerTypeLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5106_ = stack[0].m_obj;
lean_object* v_a_5107_ = stack[1].m_obj;
lean_object* v_a_5108_ = stack[2].m_obj;
lean_object* v_a_5109_ = stack[3].m_obj;
lean_object* v_a_5110_ = stack[4].m_obj;
lean_object* v_res_5146_;
v_res_5146_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
stack->m_obj
 = v_res_5146_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_);
lean_dec(v_a_5151_);
lean_dec_ref(v_a_5150_);
lean_dec(v_a_5149_);
lean_dec_ref(v_a_5148_);
return v_res_5153_;
}
}
lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5175_; 
v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5163_ = v___x_5160_;
v_isShared_5164_ = v_isSharedCheck_5175_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5160_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5175_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
if (lean_obj_tag(v_a_5161_) == 0)
{
uint8_t v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5168_; 
v___x_5165_ = 0;
v___x_5166_ = lean_box(v___x_5165_);
if (v_isShared_5164_ == 0)
{
lean_ctor_set(v___x_5163_, 0, v___x_5166_);
v___x_5168_ = v___x_5163_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
else
{
uint8_t v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5173_; 
lean_dec_ref_known(v_a_5161_, 1);
v___x_5170_ = 1;
v___x_5171_ = lean_box(v___x_5170_);
if (v_isShared_5164_ == 0)
{
lean_ctor_set(v___x_5163_, 0, v___x_5171_);
v___x_5173_ = v___x_5163_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
else
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5183_; 
v_a_5176_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5183_ == 0)
{
v___x_5178_ = v___x_5160_;
v_isShared_5179_ = v_isSharedCheck_5183_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5160_);
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
v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_Meta_isTypeFormerType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5154_ = stack[0].m_obj;
lean_object* v_a_5155_ = stack[1].m_obj;
lean_object* v_a_5156_ = stack[2].m_obj;
lean_object* v_a_5157_ = stack[3].m_obj;
lean_object* v_a_5158_ = stack[4].m_obj;
lean_object* v_res_5184_;
v_res_5184_ = l_Lean_Meta_isTypeFormerType(v_type_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_);
stack->m_obj
 = v_res_5184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Lean_Meta_isTypeFormerType(v_type_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
lean_dec(v_a_5189_);
lean_dec_ref(v_a_5188_);
lean_dec(v_a_5187_);
lean_dec_ref(v_a_5186_);
return v_res_5191_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5192_, lean_object* v_x_5193_){
_start:
{
if (lean_obj_tag(v_x_5192_) == 0)
{
if (lean_obj_tag(v_x_5193_) == 0)
{
uint8_t v___x_5194_; 
v___x_5194_ = 1;
return v___x_5194_;
}
else
{
uint8_t v___x_5195_; 
v___x_5195_ = 0;
return v___x_5195_;
}
}
else
{
if (lean_obj_tag(v_x_5193_) == 0)
{
uint8_t v___x_5196_; 
v___x_5196_ = 0;
return v___x_5196_;
}
else
{
lean_object* v_val_5197_; lean_object* v_val_5198_; uint8_t v___x_5199_; 
v_val_5197_ = lean_ctor_get(v_x_5192_, 0);
v_val_5198_ = lean_ctor_get(v_x_5193_, 0);
v___x_5199_ = lean_level_eq(v_val_5197_, v_val_5198_);
return v___x_5199_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5192_ = stack[0].m_obj;
lean_object* v_x_5193_ = stack[1].m_obj;
uint8_t v_res_5200_;
v_res_5200_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5192_, v_x_5193_);
stack->m_num = v_res_5200_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5201_, lean_object* v_x_5202_){
_start:
{
uint8_t v_res_5203_; lean_object* v_r_5204_; 
v_res_5203_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5201_, v_x_5202_);
lean_dec(v_x_5202_);
lean_dec(v_x_5201_);
v_r_5204_ = lean_box(v_res_5203_);
return v_r_5204_;
}
}
lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_){
_start:
{
lean_object* v___x_5213_; 
v___x_5213_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5224_; 
v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5216_ = v___x_5213_;
v_isShared_5217_ = v_isSharedCheck_5224_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5213_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5224_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5218_; uint8_t v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5222_; 
v___x_5218_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5219_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5214_, v___x_5218_);
lean_dec(v_a_5214_);
v___x_5220_ = lean_box(v___x_5219_);
if (v_isShared_5217_ == 0)
{
lean_ctor_set(v___x_5216_, 0, v___x_5220_);
v___x_5222_ = v___x_5216_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5220_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
v_a_5225_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5213_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5213_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isPropFormerType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5207_ = stack[0].m_obj;
lean_object* v_a_5208_ = stack[1].m_obj;
lean_object* v_a_5209_ = stack[2].m_obj;
lean_object* v_a_5210_ = stack[3].m_obj;
lean_object* v_a_5211_ = stack[4].m_obj;
lean_object* v_res_5233_;
v_res_5233_ = l_Lean_Meta_isPropFormerType(v_type_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_);
stack->m_obj
 = v_res_5233_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Lean_Meta_isPropFormerType(v_type_5234_, v_a_5235_, v_a_5236_, v_a_5237_, v_a_5238_);
lean_dec(v_a_5238_);
lean_dec_ref(v_a_5237_);
lean_dec(v_a_5236_);
lean_dec_ref(v_a_5235_);
return v_res_5240_;
}
}
lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_){
_start:
{
lean_object* v___x_5247_; 
lean_inc(v_a_5245_);
lean_inc_ref(v_a_5244_);
lean_inc(v_a_5243_);
lean_inc_ref(v_a_5242_);
v___x_5247_ = lean_infer_type(v_e_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___x_5249_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref_known(v___x_5247_, 1);
v___x_5249_ = l_Lean_Meta_isTypeFormerType(v_a_5248_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_);
return v___x_5249_;
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
v_a_5250_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5247_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5247_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5255_; 
if (v_isShared_5253_ == 0)
{
v___x_5255_ = v___x_5252_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5250_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_isTypeFormer_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5241_ = stack[0].m_obj;
lean_object* v_a_5242_ = stack[1].m_obj;
lean_object* v_a_5243_ = stack[2].m_obj;
lean_object* v_a_5244_ = stack[3].m_obj;
lean_object* v_a_5245_ = stack[4].m_obj;
lean_object* v_res_5258_;
v_res_5258_ = l_Lean_Meta_isTypeFormer(v_e_5241_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_);
stack->m_obj
 = v_res_5258_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l_Lean_Meta_isTypeFormer(v_e_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
return v_res_5265_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5266_, lean_object* v_maxFVars_x3f_5267_, lean_object* v_k_5268_, uint8_t v_cleanupAnnotations_5269_, uint8_t v_whnfType_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v___f_5276_; lean_object* v___x_5277_; 
v___f_5276_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5276_, 0, v_k_5268_);
v___x_5277_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5266_, v_maxFVars_x3f_5267_, v___f_5276_, v_cleanupAnnotations_5269_, v_whnfType_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5285_; 
v_a_5278_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5285_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5285_ == 0)
{
v___x_5280_ = v___x_5277_;
v_isShared_5281_ = v_isSharedCheck_5285_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_a_5278_);
lean_dec(v___x_5277_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5285_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v___x_5283_; 
if (v_isShared_5281_ == 0)
{
v___x_5283_ = v___x_5280_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_a_5278_);
v___x_5283_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
return v___x_5283_;
}
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
v_a_5286_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___x_5277_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5277_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5266_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_5267_ = stack[1].m_obj;
lean_object* v_k_5268_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_5269_ = stack[3].m_num;
uint8_t v_whnfType_5270_ = stack[4].m_num;
lean_object* v___y_5271_ = stack[5].m_obj;
lean_object* v___y_5272_ = stack[6].m_obj;
lean_object* v___y_5273_ = stack[7].m_obj;
lean_object* v___y_5274_ = stack[8].m_obj;
lean_object* v_res_5294_;
v_res_5294_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5266_, v_maxFVars_x3f_5267_, v_k_5268_, v_cleanupAnnotations_5269_, v_whnfType_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_);
stack->m_obj
 = v_res_5294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5295_, lean_object* v_maxFVars_x3f_5296_, lean_object* v_k_5297_, lean_object* v_cleanupAnnotations_5298_, lean_object* v_whnfType_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5305_; uint8_t v_whnfType_boxed_5306_; lean_object* v_res_5307_; 
v_cleanupAnnotations_boxed_5305_ = lean_unbox(v_cleanupAnnotations_5298_);
v_whnfType_boxed_5306_ = lean_unbox(v_whnfType_5299_);
v_res_5307_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5295_, v_maxFVars_x3f_5296_, v_k_5297_, v_cleanupAnnotations_boxed_5305_, v_whnfType_boxed_5306_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
return v_res_5307_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5308_, lean_object* v_type_5309_, lean_object* v_maxFVars_x3f_5310_, lean_object* v_k_5311_, uint8_t v_cleanupAnnotations_5312_, uint8_t v_whnfType_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
lean_object* v___x_5319_; 
v___x_5319_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5309_, v_maxFVars_x3f_5310_, v_k_5311_, v_cleanupAnnotations_5312_, v_whnfType_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
return v___x_5319_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5309_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_5310_ = stack[2].m_obj;
lean_object* v_k_5311_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_5312_ = stack[4].m_num;
uint8_t v_whnfType_5313_ = stack[5].m_num;
lean_object* v___y_5314_ = stack[6].m_obj;
lean_object* v___y_5315_ = stack[7].m_obj;
lean_object* v___y_5316_ = stack[8].m_obj;
lean_object* v___y_5317_ = stack[9].m_obj;
lean_object* v_res_5320_;
v_res_5320_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_box(0), v_type_5309_, v_maxFVars_x3f_5310_, v_k_5311_, v_cleanupAnnotations_5312_, v_whnfType_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
stack->m_obj
 = v_res_5320_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5321_, lean_object* v_type_5322_, lean_object* v_maxFVars_x3f_5323_, lean_object* v_k_5324_, lean_object* v_cleanupAnnotations_5325_, lean_object* v_whnfType_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5332_; uint8_t v_whnfType_boxed_5333_; lean_object* v_res_5334_; 
v_cleanupAnnotations_boxed_5332_ = lean_unbox(v_cleanupAnnotations_5325_);
v_whnfType_boxed_5333_ = lean_unbox(v_whnfType_5326_);
v_res_5334_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5321_, v_type_5322_, v_maxFVars_x3f_5323_, v_k_5324_, v_cleanupAnnotations_boxed_5332_, v_whnfType_boxed_5333_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
return v_res_5334_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5335_, lean_object* v_as_5336_, size_t v_i_5337_, size_t v_stop_5338_){
_start:
{
uint8_t v___x_5339_; 
v___x_5339_ = lean_usize_dec_eq(v_i_5337_, v_stop_5338_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; uint8_t v___x_5341_; 
v___x_5340_ = lean_array_uget_borrowed(v_as_5336_, v_i_5337_);
v___x_5341_ = lean_expr_eqv(v_a_5335_, v___x_5340_);
if (v___x_5341_ == 0)
{
size_t v___x_5342_; size_t v___x_5343_; 
v___x_5342_ = ((size_t)1ULL);
v___x_5343_ = lean_usize_add(v_i_5337_, v___x_5342_);
v_i_5337_ = v___x_5343_;
goto _start;
}
else
{
return v___x_5341_;
}
}
else
{
uint8_t v___x_5345_; 
v___x_5345_ = 0;
return v___x_5345_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5335_ = stack[0].m_obj;
lean_object* v_as_5336_ = stack[1].m_obj;
size_t v_i_5337_ = stack[2].m_num;
size_t v_stop_5338_ = stack[3].m_num;
uint8_t v_res_5346_;
v_res_5346_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5335_, v_as_5336_, v_i_5337_, v_stop_5338_);
stack->m_num = v_res_5346_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5347_, lean_object* v_as_5348_, lean_object* v_i_5349_, lean_object* v_stop_5350_){
_start:
{
size_t v_i_boxed_5351_; size_t v_stop_boxed_5352_; uint8_t v_res_5353_; lean_object* v_r_5354_; 
v_i_boxed_5351_ = lean_unbox_usize(v_i_5349_);
lean_dec(v_i_5349_);
v_stop_boxed_5352_ = lean_unbox_usize(v_stop_5350_);
lean_dec(v_stop_5350_);
v_res_5353_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5347_, v_as_5348_, v_i_boxed_5351_, v_stop_boxed_5352_);
lean_dec_ref(v_as_5348_);
lean_dec_ref(v_a_5347_);
v_r_5354_ = lean_box(v_res_5353_);
return v_r_5354_;
}
}
uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5355_, lean_object* v_a_5356_){
_start:
{
lean_object* v___x_5357_; lean_object* v___x_5358_; uint8_t v___x_5359_; 
v___x_5357_ = lean_unsigned_to_nat(0u);
v___x_5358_ = lean_array_get_size(v_as_5355_);
v___x_5359_ = lean_nat_dec_lt(v___x_5357_, v___x_5358_);
if (v___x_5359_ == 0)
{
return v___x_5359_;
}
else
{
if (v___x_5359_ == 0)
{
return v___x_5359_;
}
else
{
size_t v___x_5360_; size_t v___x_5361_; uint8_t v___x_5362_; 
v___x_5360_ = ((size_t)0ULL);
v___x_5361_ = lean_usize_of_nat(v___x_5358_);
v___x_5362_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5356_, v_as_5355_, v___x_5360_, v___x_5361_);
return v___x_5362_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5355_ = stack[0].m_obj;
lean_object* v_a_5356_ = stack[1].m_obj;
uint8_t v_res_5363_;
v_res_5363_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5355_, v_a_5356_);
stack->m_num = v_res_5363_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5364_, lean_object* v_a_5365_){
_start:
{
uint8_t v_res_5366_; lean_object* v_r_5367_; 
v_res_5366_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5364_, v_a_5365_);
lean_dec_ref(v_a_5365_);
lean_dec_ref(v_as_5364_);
v_r_5367_ = lean_box(v_res_5366_);
return v_r_5367_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5368_, lean_object* v_e_5369_){
_start:
{
uint8_t v___x_5370_; lean_object* v_d_5372_; lean_object* v_b_5373_; 
v___x_5370_ = l_Lean_Expr_hasFVar(v_e_5369_);
if (v___x_5370_ == 0)
{
lean_dec_ref(v_e_5369_);
return v___x_5370_;
}
else
{
switch(lean_obj_tag(v_e_5369_))
{
case 7:
{
lean_object* v_binderType_5376_; lean_object* v_body_5377_; 
v_binderType_5376_ = lean_ctor_get(v_e_5369_, 1);
lean_inc_ref(v_binderType_5376_);
v_body_5377_ = lean_ctor_get(v_e_5369_, 2);
lean_inc_ref(v_body_5377_);
lean_dec_ref_known(v_e_5369_, 3);
v_d_5372_ = v_binderType_5376_;
v_b_5373_ = v_body_5377_;
goto v___jp_5371_;
}
case 6:
{
lean_object* v_binderType_5378_; lean_object* v_body_5379_; 
v_binderType_5378_ = lean_ctor_get(v_e_5369_, 1);
lean_inc_ref(v_binderType_5378_);
v_body_5379_ = lean_ctor_get(v_e_5369_, 2);
lean_inc_ref(v_body_5379_);
lean_dec_ref_known(v_e_5369_, 3);
v_d_5372_ = v_binderType_5378_;
v_b_5373_ = v_body_5379_;
goto v___jp_5371_;
}
case 10:
{
lean_object* v_expr_5380_; 
v_expr_5380_ = lean_ctor_get(v_e_5369_, 1);
lean_inc_ref(v_expr_5380_);
lean_dec_ref_known(v_e_5369_, 2);
v_e_5369_ = v_expr_5380_;
goto _start;
}
case 8:
{
lean_object* v_type_5382_; lean_object* v_value_5383_; lean_object* v_body_5384_; uint8_t v___x_5385_; 
v_type_5382_ = lean_ctor_get(v_e_5369_, 1);
lean_inc_ref(v_type_5382_);
v_value_5383_ = lean_ctor_get(v_e_5369_, 2);
lean_inc_ref(v_value_5383_);
v_body_5384_ = lean_ctor_get(v_e_5369_, 3);
lean_inc_ref(v_body_5384_);
lean_dec_ref_known(v_e_5369_, 4);
v___x_5385_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5368_, v_type_5382_);
if (v___x_5385_ == 0)
{
uint8_t v___x_5386_; 
v___x_5386_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5368_, v_value_5383_);
if (v___x_5386_ == 0)
{
v_e_5369_ = v_body_5384_;
goto _start;
}
else
{
lean_dec_ref(v_body_5384_);
return v___x_5370_;
}
}
else
{
lean_dec_ref(v_body_5384_);
lean_dec_ref(v_value_5383_);
return v___x_5370_;
}
}
case 5:
{
lean_object* v_fn_5388_; lean_object* v_arg_5389_; uint8_t v___x_5390_; 
v_fn_5388_ = lean_ctor_get(v_e_5369_, 0);
lean_inc_ref(v_fn_5388_);
v_arg_5389_ = lean_ctor_get(v_e_5369_, 1);
lean_inc_ref(v_arg_5389_);
lean_dec_ref_known(v_e_5369_, 2);
v___x_5390_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5368_, v_fn_5388_);
if (v___x_5390_ == 0)
{
v_e_5369_ = v_arg_5389_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5389_);
return v___x_5370_;
}
}
case 11:
{
lean_object* v_struct_5392_; 
v_struct_5392_ = lean_ctor_get(v_e_5369_, 2);
lean_inc_ref(v_struct_5392_);
lean_dec_ref_known(v_e_5369_, 3);
v_e_5369_ = v_struct_5392_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5394_; lean_object* v___x_5395_; uint8_t v___x_5396_; 
v_fvarId_5394_ = lean_ctor_get(v_e_5369_, 0);
lean_inc(v_fvarId_5394_);
lean_dec_ref_known(v_e_5369_, 1);
v___x_5395_ = l_Lean_Expr_fvar___override(v_fvarId_5394_);
v___x_5396_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5368_, v___x_5395_);
lean_dec_ref(v___x_5395_);
return v___x_5396_;
}
default: 
{
uint8_t v___x_5397_; 
lean_dec_ref(v_e_5369_);
v___x_5397_ = 0;
return v___x_5397_;
}
}
}
v___jp_5371_:
{
uint8_t v___x_5374_; 
v___x_5374_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5368_, v_d_5372_);
if (v___x_5374_ == 0)
{
v_e_5369_ = v_b_5373_;
goto _start;
}
else
{
lean_dec_ref(v_b_5373_);
return v___x_5370_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5368_ = stack[0].m_obj;
lean_object* v_e_5369_ = stack[1].m_obj;
uint8_t v_res_5398_;
v_res_5398_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5368_, v_e_5369_);
stack->m_num = v_res_5398_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5399_, lean_object* v_e_5400_){
_start:
{
uint8_t v_res_5401_; lean_object* v_r_5402_; 
v_res_5401_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5399_, v_e_5400_);
lean_dec_ref(v_xs_5399_);
v_r_5402_ = lean_box(v_res_5401_);
return v_r_5402_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5405_ = l_Lean_stringToMessageData(v___x_5404_);
return v___x_5405_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5408_ = l_Lean_stringToMessageData(v___x_5407_);
return v___x_5408_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5409_, lean_object* v_type_5410_, lean_object* v_as_5411_, size_t v_sz_5412_, size_t v_i_5413_, lean_object* v_b_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
lean_object* v_a_5421_; uint8_t v___x_5425_; 
v___x_5425_ = lean_usize_dec_lt(v_i_5413_, v_sz_5412_);
if (v___x_5425_ == 0)
{
lean_object* v___x_5426_; 
lean_dec_ref(v_type_5410_);
v___x_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5426_, 0, v_b_5414_);
return v___x_5426_;
}
else
{
lean_object* v___x_5427_; lean_object* v_a_5428_; uint8_t v___x_5429_; 
v___x_5427_ = lean_box(0);
v_a_5428_ = lean_array_uget_borrowed(v_as_5411_, v_i_5413_);
lean_inc(v_a_5428_);
v___x_5429_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5409_, v_a_5428_);
if (v___x_5429_ == 0)
{
v_a_5421_ = v___x_5427_;
goto v___jp_5420_;
}
else
{
lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5430_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5428_);
v___x_5431_ = l_Lean_MessageData_ofExpr(v_a_5428_);
v___x_5432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5430_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5434_, 0, v___x_5432_);
lean_ctor_set(v___x_5434_, 1, v___x_5433_);
lean_inc_ref(v_type_5410_);
v___x_5435_ = l_Lean_MessageData_ofExpr(v_type_5410_);
v___x_5436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5436_, 0, v___x_5434_);
lean_ctor_set(v___x_5436_, 1, v___x_5435_);
v___x_5437_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5436_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
if (lean_obj_tag(v___x_5437_) == 0)
{
lean_dec_ref_known(v___x_5437_, 1);
v_a_5421_ = v___x_5427_;
goto v___jp_5420_;
}
else
{
lean_dec_ref(v_type_5410_);
return v___x_5437_;
}
}
}
v___jp_5420_:
{
size_t v___x_5422_; size_t v___x_5423_; 
v___x_5422_ = ((size_t)1ULL);
v___x_5423_ = lean_usize_add(v_i_5413_, v___x_5422_);
v_i_5413_ = v___x_5423_;
v_b_5414_ = v_a_5421_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5409_ = stack[0].m_obj;
lean_object* v_type_5410_ = stack[1].m_obj;
lean_object* v_as_5411_ = stack[2].m_obj;
size_t v_sz_5412_ = stack[3].m_num;
size_t v_i_5413_ = stack[4].m_num;
lean_object* v_b_5414_ = stack[5].m_obj;
lean_object* v___y_5415_ = stack[6].m_obj;
lean_object* v___y_5416_ = stack[7].m_obj;
lean_object* v___y_5417_ = stack[8].m_obj;
lean_object* v___y_5418_ = stack[9].m_obj;
lean_object* v_res_5438_;
v_res_5438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5409_, v_type_5410_, v_as_5411_, v_sz_5412_, v_i_5413_, v_b_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
stack->m_obj
 = v_res_5438_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5439_, lean_object* v_type_5440_, lean_object* v_as_5441_, lean_object* v_sz_5442_, lean_object* v_i_5443_, lean_object* v_b_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
size_t v_sz_boxed_5450_; size_t v_i_boxed_5451_; lean_object* v_res_5452_; 
v_sz_boxed_5450_ = lean_unbox_usize(v_sz_5442_);
lean_dec(v_sz_5442_);
v_i_boxed_5451_ = lean_unbox_usize(v_i_5443_);
lean_dec(v_i_5443_);
v_res_5452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5439_, v_type_5440_, v_as_5441_, v_sz_boxed_5450_, v_i_boxed_5451_, v_b_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec_ref(v_as_5441_);
lean_dec_ref(v_xs_5439_);
return v_res_5452_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5453_, size_t v_i_5454_, lean_object* v_bs_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
uint8_t v___x_5461_; 
v___x_5461_ = lean_usize_dec_lt(v_i_5454_, v_sz_5453_);
if (v___x_5461_ == 0)
{
lean_object* v___x_5462_; 
v___x_5462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5462_, 0, v_bs_5455_);
return v___x_5462_;
}
else
{
lean_object* v_v_5463_; lean_object* v___x_5464_; lean_object* v_bs_x27_5465_; lean_object* v___x_5466_; 
v_v_5463_ = lean_array_uget(v_bs_5455_, v_i_5454_);
v___x_5464_ = lean_unsigned_to_nat(0u);
v_bs_x27_5465_ = lean_array_uset(v_bs_5455_, v_i_5454_, v___x_5464_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
v___x_5466_ = lean_infer_type(v_v_5463_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; size_t v___x_5468_; size_t v___x_5469_; lean_object* v___x_5470_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
lean_inc(v_a_5467_);
lean_dec_ref_known(v___x_5466_, 1);
v___x_5468_ = ((size_t)1ULL);
v___x_5469_ = lean_usize_add(v_i_5454_, v___x_5468_);
v___x_5470_ = lean_array_uset(v_bs_x27_5465_, v_i_5454_, v_a_5467_);
v_i_5454_ = v___x_5469_;
v_bs_5455_ = v___x_5470_;
goto _start;
}
else
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5479_; 
lean_dec_ref(v_bs_x27_5465_);
v_a_5472_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5474_ = v___x_5466_;
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___x_5466_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5477_; 
if (v_isShared_5475_ == 0)
{
v___x_5477_ = v___x_5474_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
return v___x_5477_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_5453_ = stack[0].m_num;
size_t v_i_5454_ = stack[1].m_num;
lean_object* v_bs_5455_ = stack[2].m_obj;
lean_object* v___y_5456_ = stack[3].m_obj;
lean_object* v___y_5457_ = stack[4].m_obj;
lean_object* v___y_5458_ = stack[5].m_obj;
lean_object* v___y_5459_ = stack[6].m_obj;
lean_object* v_res_5480_;
v_res_5480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5453_, v_i_5454_, v_bs_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
stack->m_obj
 = v_res_5480_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5481_, lean_object* v_i_5482_, lean_object* v_bs_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_){
_start:
{
size_t v_sz_boxed_5489_; size_t v_i_boxed_5490_; lean_object* v_res_5491_; 
v_sz_boxed_5489_ = lean_unbox_usize(v_sz_5481_);
lean_dec(v_sz_5481_);
v_i_boxed_5490_ = lean_unbox_usize(v_i_5482_);
lean_dec(v_i_5482_);
v_res_5491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5489_, v_i_boxed_5490_, v_bs_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
lean_dec(v___y_5487_);
lean_dec_ref(v___y_5486_);
lean_dec(v___y_5485_);
lean_dec_ref(v___y_5484_);
return v_res_5491_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___x_5493_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5494_ = l_Lean_stringToMessageData(v___x_5493_);
return v___x_5494_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5496_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5497_ = l_Lean_stringToMessageData(v___x_5496_);
return v___x_5497_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5499_; lean_object* v___x_5500_; 
v___x_5499_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5500_ = l_Lean_stringToMessageData(v___x_5499_);
return v___x_5500_;
}
}
lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5501_, lean_object* v_n_5502_, lean_object* v_xs_5503_, lean_object* v_x_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_){
_start:
{
lean_object* v___x_5534_; uint8_t v___x_5535_; 
v___x_5534_ = lean_array_get_size(v_xs_5503_);
v___x_5535_ = lean_nat_dec_eq(v___x_5534_, v_n_5502_);
if (v___x_5535_ == 0)
{
lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5555_; 
lean_dec_ref(v_xs_5503_);
v___x_5536_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5537_ = l_Lean_MessageData_ofExpr(v_type_5501_);
v___x_5538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5536_);
lean_ctor_set(v___x_5538_, 1, v___x_5537_);
v___x_5539_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5540_, 0, v___x_5538_);
lean_ctor_set(v___x_5540_, 1, v___x_5539_);
v___x_5541_ = l_Nat_reprFast(v_n_5502_);
v___x_5542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5541_);
v___x_5543_ = l_Lean_MessageData_ofFormat(v___x_5542_);
v___x_5544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5540_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
v___x_5545_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5544_);
lean_ctor_set(v___x_5546_, 1, v___x_5545_);
v___x_5547_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5546_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_);
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5555_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5550_ = v___x_5547_;
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5547_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5553_; 
if (v_isShared_5551_ == 0)
{
v___x_5553_ = v___x_5550_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_a_5548_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
return v___x_5553_;
}
}
}
else
{
lean_dec(v_n_5502_);
goto v___jp_5510_;
}
v___jp_5510_:
{
size_t v_sz_5511_; size_t v___x_5512_; lean_object* v___x_5513_; 
v_sz_5511_ = lean_array_size(v_xs_5503_);
v___x_5512_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5503_);
v___x_5513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5511_, v___x_5512_, v_xs_5503_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_);
if (lean_obj_tag(v___x_5513_) == 0)
{
lean_object* v_a_5514_; lean_object* v___x_5515_; size_t v_sz_5516_; lean_object* v___x_5517_; 
v_a_5514_ = lean_ctor_get(v___x_5513_, 0);
lean_inc(v_a_5514_);
lean_dec_ref_known(v___x_5513_, 1);
v___x_5515_ = lean_box(0);
v_sz_5516_ = lean_array_size(v_a_5514_);
v___x_5517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5503_, v_type_5501_, v_a_5514_, v_sz_5516_, v___x_5512_, v___x_5515_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_);
lean_dec_ref(v_xs_5503_);
if (lean_obj_tag(v___x_5517_) == 0)
{
lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5524_; 
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5517_);
if (v_isSharedCheck_5524_ == 0)
{
lean_object* v_unused_5525_; 
v_unused_5525_ = lean_ctor_get(v___x_5517_, 0);
lean_dec(v_unused_5525_);
v___x_5519_ = v___x_5517_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_dec(v___x_5517_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 0, v_a_5514_);
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_a_5514_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
lean_dec(v_a_5514_);
v_a_5526_ = lean_ctor_get(v___x_5517_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5517_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v___x_5517_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5517_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5503_);
lean_dec_ref(v_type_5501_);
return v___x_5513_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_arrowDomainsN___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_5501_ = stack[0].m_obj;
lean_object* v_n_5502_ = stack[1].m_obj;
lean_object* v_xs_5503_ = stack[2].m_obj;
lean_object* v_x_5504_ = stack[3].m_obj;
lean_object* v___y_5505_ = stack[4].m_obj;
lean_object* v___y_5506_ = stack[5].m_obj;
lean_object* v___y_5507_ = stack[6].m_obj;
lean_object* v___y_5508_ = stack[7].m_obj;
lean_object* v_res_5556_;
v_res_5556_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5501_, v_n_5502_, v_xs_5503_, v_x_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_);
stack->m_obj
 = v_res_5556_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5557_, lean_object* v_n_5558_, lean_object* v_xs_5559_, lean_object* v_x_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_){
_start:
{
lean_object* v_res_5566_; 
v_res_5566_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5557_, v_n_5558_, v_xs_5559_, v_x_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
lean_dec_ref(v_x_5560_);
return v_res_5566_;
}
}
lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5567_, lean_object* v_type_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_){
_start:
{
lean_object* v___f_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; lean_object* v___x_5577_; 
lean_inc(v_n_5567_);
lean_inc_ref(v_type_5568_);
v___f_5574_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5574_, 0, v_type_5568_);
lean_closure_set(v___f_5574_, 1, v_n_5567_);
v___x_5575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5575_, 0, v_n_5567_);
v___x_5576_ = 0;
v___x_5577_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5568_, v___x_5575_, v___f_5574_, v___x_5576_, v___x_5576_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_);
return v___x_5577_;
}
}
LEAN_EXPORT void l_Lean_Meta_arrowDomainsN_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_5567_ = stack[0].m_obj;
lean_object* v_type_5568_ = stack[1].m_obj;
lean_object* v_a_5569_ = stack[2].m_obj;
lean_object* v_a_5570_ = stack[3].m_obj;
lean_object* v_a_5571_ = stack[4].m_obj;
lean_object* v_a_5572_ = stack[5].m_obj;
lean_object* v_res_5578_;
v_res_5578_ = l_Lean_Meta_arrowDomainsN(v_n_5567_, v_type_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_);
stack->m_obj
 = v_res_5578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5579_, lean_object* v_type_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_){
_start:
{
lean_object* v_res_5586_; 
v_res_5586_ = l_Lean_Meta_arrowDomainsN(v_n_5579_, v_type_5580_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_);
lean_dec(v_a_5584_);
lean_dec_ref(v_a_5583_);
lean_dec(v_a_5582_);
lean_dec_ref(v_a_5581_);
return v_res_5586_;
}
}
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5587_, lean_object* v_e_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_){
_start:
{
lean_object* v___x_5594_; 
lean_inc(v_a_5592_);
lean_inc_ref(v_a_5591_);
lean_inc(v_a_5590_);
lean_inc_ref(v_a_5589_);
v___x_5594_ = lean_infer_type(v_e_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_a_5595_; lean_object* v___x_5596_; 
v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
lean_inc(v_a_5595_);
lean_dec_ref_known(v___x_5594_, 1);
v___x_5596_ = l_Lean_Meta_arrowDomainsN(v_n_5587_, v_a_5595_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_);
return v___x_5596_;
}
else
{
lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5604_; 
lean_dec(v_n_5587_);
v_a_5597_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5599_ = v___x_5594_;
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_dec(v___x_5594_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5602_; 
if (v_isShared_5600_ == 0)
{
v___x_5602_ = v___x_5599_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_inferArgumentTypesN_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_5587_ = stack[0].m_obj;
lean_object* v_e_5588_ = stack[1].m_obj;
lean_object* v_a_5589_ = stack[2].m_obj;
lean_object* v_a_5590_ = stack[3].m_obj;
lean_object* v_a_5591_ = stack[4].m_obj;
lean_object* v_a_5592_ = stack[5].m_obj;
lean_object* v_res_5605_;
v_res_5605_ = l_Lean_Meta_inferArgumentTypesN(v_n_5587_, v_e_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_);
stack->m_obj
 = v_res_5605_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5606_, lean_object* v_e_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_){
_start:
{
lean_object* v_res_5613_; 
v_res_5613_ = l_Lean_Meta_inferArgumentTypesN(v_n_5606_, v_e_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_);
lean_dec(v_a_5611_);
lean_dec_ref(v_a_5610_);
lean_dec(v_a_5609_);
lean_dec_ref(v_a_5608_);
return v_res_5613_;
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
