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
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
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
v___x_1048_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1035_, v_declHint_1030_);
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
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1090_; 
v_val_1056_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1058_ = v___x_1048_;
v_isShared_1059_ = v_isSharedCheck_1090_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v___x_1048_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1090_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_mod_1062_; uint8_t v___x_1063_; 
v___x_1060_ = l_Lean_Environment_header(v_env_1035_);
lean_dec_ref(v_env_1035_);
v___x_1061_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1060_);
v_mod_1062_ = lean_array_get(v___x_1033_, v___x_1061_, v_val_1056_);
lean_dec(v_val_1056_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = l_Lean_isPrivateName(v_declHint_1030_);
lean_dec(v_declHint_1030_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_c_1047_);
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = l_Lean_MessageData_ofName(v_mod_1062_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_MessageData_note(v___x_1071_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_msg_1029_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1073_);
v___x_1075_ = v___x_1058_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_c_1047_);
v___x_1079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_MessageData_ofName(v_mod_1062_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_MessageData_note(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_msg_1029_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1086_);
v___x_1088_ = v___x_1058_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1091_; 
lean_dec_ref(v_env_1035_);
lean_dec(v_declHint_1030_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_msg_1029_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1092_, lean_object* v_declHint_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1092_, v_declHint_1093_, v___y_1094_);
lean_dec(v___y_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1097_, lean_object* v_declHint_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
v___x_1104_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1097_, v_declHint_1098_, v___y_1102_);
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1109_ = l_Lean_unknownIdentifierMessageTag;
v___x_1110_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_a_1105_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1110_);
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1115_, lean_object* v_declHint_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1115_, v_declHint_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1123_, lean_object* v_msg_1124_, lean_object* v_declHint_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_a_1132_; lean_object* v___x_1133_; 
v___x_1131_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1124_, v_declHint_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v___x_1131_);
v___x_1133_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1123_, v_a_1132_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1134_, lean_object* v_msg_1135_, lean_object* v_declHint_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1134_, v_msg_1135_, v_declHint_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v_ref_1134_);
return v_res_1142_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1145_ = l_Lean_stringToMessageData(v___x_1144_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1149_, lean_object* v_constName_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1156_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1157_ = 0;
lean_inc(v_constName_1150_);
v___x_1158_ = l_Lean_MessageData_ofConstName(v_constName_1150_, v___x_1157_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1156_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1149_, v___x_1161_, v_constName_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1163_, lean_object* v_constName_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1163_, v_constName_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v_ref_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_ref_1177_; lean_object* v___x_1178_; 
v_ref_1177_ = lean_ctor_get(v___y_1174_, 2);
v___x_1178_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1177_, v_constName_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = lean_st_ref_get(v___y_1190_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1194_ = 0;
lean_inc(v_constName_1186_);
v___x_1195_ = l_Lean_Environment_findConstVal_x3f(v_env_1193_, v_constName_1186_, v___x_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1196_;
}
else
{
lean_object* v_val_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_constName_1186_);
v_val_1197_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_val_1197_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set_tag(v___x_1199_, 0);
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_val_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1212_, lean_object* v_us_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; 
lean_inc(v_c_1212_);
v___x_1219_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1212_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v_levelParams_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v_levelParams_1221_ = lean_ctor_get(v_a_1220_, 1);
v___x_1222_ = l_List_lengthTR___redArg(v_levelParams_1221_);
v___x_1223_ = l_List_lengthTR___redArg(v_us_1213_);
v___x_1224_ = lean_nat_dec_eq(v___x_1222_, v___x_1223_);
lean_dec(v___x_1223_);
lean_dec(v___x_1222_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec(v_a_1220_);
v___x_1225_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1212_, v_us_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; 
lean_dec(v_c_1212_);
v___x_1226_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1220_, v_us_1213_, v_a_1217_);
return v___x_1226_;
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_us_1213_);
lean_dec(v_c_1212_);
v_a_1227_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1219_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1219_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1235_, lean_object* v_us_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1235_, v_us_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1243_, lean_object* v_constName_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_constName_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1251_, v_constName_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1259_, lean_object* v_ref_1260_, lean_object* v_constName_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1260_, v_constName_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1268_, lean_object* v_ref_1269_, lean_object* v_constName_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1268_, v_ref_1269_, v_constName_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v_ref_1269_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1277_, lean_object* v_ref_1278_, lean_object* v_msg_1279_, lean_object* v_declHint_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1278_, v_msg_1279_, v_declHint_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1287_, lean_object* v_ref_1288_, lean_object* v_msg_1289_, lean_object* v_declHint_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1287_, v_ref_1288_, v_msg_1289_, v_declHint_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v_ref_1288_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1297_, lean_object* v_declHint_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1297_, v_declHint_1298_, v___y_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1305_, lean_object* v_declHint_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1305_, v_declHint_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1313_, lean_object* v_ref_1314_, lean_object* v_msg_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1314_, v_msg_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1322_, lean_object* v_ref_1323_, lean_object* v_msg_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1322_, v_ref_1323_, v_msg_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v_ref_1323_);
return v_res_1330_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1336_ = l_Lean_stringToMessageData(v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1337_, lean_object* v_idx_1338_, lean_object* v_e_1339_, lean_object* v_a_1340_, lean_object* v_00_u03b1_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1348_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1349_ = l_Lean_mkProj(v_structName_1337_, v_idx_1338_, v_e_1339_);
v___x_1350_ = l_Lean_indentExpr(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1348_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_indentExpr(v_a_1340_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1355_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1357_, lean_object* v_idx_1358_, lean_object* v_e_1359_, lean_object* v_a_1360_, lean_object* v_00_u03b1_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1357_, v_idx_1358_, v_e_1359_, v_a_1360_, v_00_u03b1_1361_, v_x_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v_env_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; 
v___x_1375_ = lean_st_ref_get(v___y_1373_);
v_env_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_env_1376_);
lean_dec(v___x_1375_);
v___x_1377_ = 0;
lean_inc(v_constName_1369_);
v___x_1378_ = l_Lean_Environment_find_x3f(v_env_1376_, v_constName_1369_, v___x_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1379_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_constName_1369_);
v_val_1380_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1378_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v___x_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 0);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_val_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1395_, lean_object* v_structName_1396_, lean_object* v_e_1397_, lean_object* v_idx_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_b_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_a_1408_; uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_lt(v_a_1400_, v_upperBound_1395_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_idx_1398_);
lean_dec_ref(v_e_1397_);
lean_dec(v_structName_1396_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_b_1401_);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; 
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
v___x_1414_ = lean_whnf(v_b_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
if (lean_obj_tag(v_a_1415_) == 7)
{
lean_object* v_body_1416_; uint8_t v___x_1417_; 
v_body_1416_ = lean_ctor_get(v_a_1415_, 2);
lean_inc_ref(v_body_1416_);
lean_dec_ref_known(v_a_1415_, 3);
v___x_1417_ = l_Lean_Expr_hasLooseBVars(v_body_1416_);
if (v___x_1417_ == 0)
{
v_a_1408_ = v_body_1416_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_inc_ref(v_e_1397_);
lean_inc(v_a_1400_);
lean_inc(v_structName_1396_);
v___x_1418_ = l_Lean_mkProj(v_structName_1396_, v_a_1400_, v_e_1397_);
v___x_1419_ = lean_expr_instantiate1(v_body_1416_, v___x_1418_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_body_1416_);
v_a_1408_ = v___x_1419_;
goto v___jp_1407_;
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1420_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1397_);
lean_inc(v_idx_1398_);
lean_inc(v_structName_1396_);
v___x_1421_ = l_Lean_mkProj(v_structName_1396_, v_idx_1398_, v_e_1397_);
v___x_1422_ = l_Lean_indentExpr(v___x_1421_);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1420_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
lean_inc_ref(v_a_1399_);
v___x_1426_ = l_Lean_indentExpr(v_a_1399_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1427_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_dec_ref_known(v___x_1428_, 1);
v_a_1408_ = v_a_1415_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_a_1415_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_idx_1398_);
lean_dec_ref(v_e_1397_);
lean_dec(v_structName_1396_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
else
{
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_idx_1398_);
lean_dec_ref(v_e_1397_);
lean_dec(v_structName_1396_);
return v___x_1414_;
}
}
v___jp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_nat_add(v_a_1400_, v___x_1409_);
lean_dec(v_a_1400_);
v_a_1400_ = v___x_1410_;
v_b_1401_ = v_a_1408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1437_, lean_object* v_structName_1438_, lean_object* v_e_1439_, lean_object* v_idx_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1437_, v_structName_1438_, v_e_1439_, v_idx_1440_, v_a_1441_, v_a_1442_, v_b_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_upperBound_1437_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1450_, lean_object* v_structName_1451_, lean_object* v_e_1452_, lean_object* v_idx_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_a_1463_; uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_lt(v_a_1455_, v_upperBound_1450_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_idx_1453_);
lean_dec_ref(v_e_1452_);
lean_dec(v_structName_1451_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_b_1456_);
return v___x_1468_;
}
else
{
lean_object* v___x_1469_; 
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
v___x_1469_ = lean_whnf(v_b_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
if (lean_obj_tag(v_a_1470_) == 7)
{
lean_object* v_body_1471_; uint8_t v___x_1472_; 
v_body_1471_ = lean_ctor_get(v_a_1470_, 2);
lean_inc_ref(v_body_1471_);
lean_dec_ref_known(v_a_1470_, 3);
v___x_1472_ = l_Lean_Expr_hasLooseBVars(v_body_1471_);
if (v___x_1472_ == 0)
{
v_a_1463_ = v_body_1471_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_inc_ref(v_e_1452_);
lean_inc(v_a_1455_);
lean_inc(v_structName_1451_);
v___x_1473_ = l_Lean_mkProj(v_structName_1451_, v_a_1455_, v_e_1452_);
v___x_1474_ = lean_expr_instantiate1(v_body_1471_, v___x_1473_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_body_1471_);
v_a_1463_ = v___x_1474_;
goto v___jp_1462_;
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1475_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1452_);
lean_inc(v_idx_1453_);
lean_inc(v_structName_1451_);
v___x_1476_ = l_Lean_mkProj(v_structName_1451_, v_idx_1453_, v_e_1452_);
v___x_1477_ = l_Lean_indentExpr(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1475_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
lean_inc_ref(v_a_1454_);
v___x_1481_ = l_Lean_indentExpr(v_a_1454_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1482_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_dec_ref_known(v___x_1483_, 1);
v_a_1463_ = v_a_1470_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_a_1470_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_idx_1453_);
lean_dec_ref(v_e_1452_);
lean_dec(v_structName_1451_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
else
{
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_idx_1453_);
lean_dec_ref(v_e_1452_);
lean_dec(v_structName_1451_);
return v___x_1469_;
}
}
v___jp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_a_1455_, v___x_1464_);
lean_dec(v_a_1455_);
v___x_1466_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1450_, v_structName_1451_, v_e_1452_, v_idx_1453_, v_a_1454_, v___x_1465_, v_a_1463_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1492_, lean_object* v_structName_1493_, lean_object* v_e_1494_, lean_object* v_idx_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1492_, v_structName_1493_, v_e_1494_, v_idx_1495_, v_a_1496_, v_a_1497_, v_b_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v_upperBound_1492_);
return v_res_1504_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1505_; lean_object* v_dummy_1506_; 
v___x_1505_ = lean_box(0);
v_dummy_1506_ = l_Lean_Expr_sort___override(v___x_1505_);
return v_dummy_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1507_, lean_object* v_idx_1508_, lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; 
lean_inc(v_a_1513_);
lean_inc_ref(v_a_1512_);
lean_inc(v_a_1511_);
lean_inc_ref(v_a_1510_);
lean_inc_ref(v_e_1509_);
v___x_1515_ = lean_infer_type(v_e_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
lean_inc(v_a_1513_);
lean_inc_ref(v_a_1512_);
lean_inc(v_a_1511_);
lean_inc_ref(v_a_1510_);
v___x_1517_ = lean_whnf(v_a_1516_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Expr_getAppFn(v_a_1518_);
if (lean_obj_tag(v___x_1519_) == 4)
{
lean_object* v_declName_1520_; lean_object* v_us_1521_; lean_object* v___x_1522_; lean_object* v_env_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; 
v_declName_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_declName_1520_);
v_us_1521_ = lean_ctor_get(v___x_1519_, 1);
lean_inc(v_us_1521_);
lean_dec_ref_known(v___x_1519_, 2);
v___x_1522_ = lean_st_ref_get(v_a_1513_);
v_env_1526_ = lean_ctor_get(v___x_1522_, 0);
lean_inc_ref(v_env_1526_);
lean_dec(v___x_1522_);
v___x_1527_ = 0;
v___x_1528_ = l_Lean_Environment_find_x3f(v_env_1526_, v_declName_1520_, v___x_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_us_1521_);
v___x_1529_ = lean_box(0);
v___x_1530_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1529_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1530_;
}
else
{
lean_object* v_val_1531_; 
v_val_1531_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v___x_1528_, 1);
if (lean_obj_tag(v_val_1531_) == 5)
{
lean_object* v_val_1532_; lean_object* v_ctors_1533_; 
v_val_1532_ = lean_ctor_get(v_val_1531_, 0);
lean_inc_ref(v_val_1532_);
lean_dec_ref_known(v_val_1531_, 1);
v_ctors_1533_ = lean_ctor_get(v_val_1532_, 4);
lean_inc(v_ctors_1533_);
if (lean_obj_tag(v_ctors_1533_) == 1)
{
lean_object* v_tail_1534_; 
v_tail_1534_ = lean_ctor_get(v_ctors_1533_, 1);
if (lean_obj_tag(v_tail_1534_) == 0)
{
lean_object* v_toConstantVal_1535_; lean_object* v_numParams_1536_; lean_object* v_numIndices_1537_; lean_object* v_head_1538_; lean_object* v___x_1539_; 
v_toConstantVal_1535_ = lean_ctor_get(v_val_1532_, 0);
lean_inc_ref(v_toConstantVal_1535_);
v_numParams_1536_ = lean_ctor_get(v_val_1532_, 1);
lean_inc(v_numParams_1536_);
v_numIndices_1537_ = lean_ctor_get(v_val_1532_, 2);
lean_inc(v_numIndices_1537_);
lean_dec_ref(v_val_1532_);
v_head_1538_ = lean_ctor_get(v_ctors_1533_, 0);
lean_inc(v_head_1538_);
lean_dec_ref_known(v_ctors_1533_, 2);
v___x_1539_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1538_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
if (lean_obj_tag(v_a_1540_) == 6)
{
lean_object* v_val_1541_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v_name_1581_; uint8_t v___x_1582_; 
v_val_1541_ = lean_ctor_get(v_a_1540_, 0);
lean_inc_ref(v_val_1541_);
lean_dec_ref_known(v_a_1540_, 1);
v_name_1581_ = lean_ctor_get(v_toConstantVal_1535_, 0);
lean_inc(v_name_1581_);
lean_dec_ref(v_toConstantVal_1535_);
v___x_1582_ = lean_name_eq(v_name_1581_, v_structName_1507_);
lean_dec(v_name_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_val_1541_);
lean_dec(v_numIndices_1537_);
lean_dec(v_numParams_1536_);
lean_dec(v_us_1521_);
v___x_1583_ = lean_box(0);
v___x_1584_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1583_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
v___y_1543_ = v_a_1510_;
v___y_1544_ = v_a_1511_;
v___y_1545_ = v_a_1512_;
v___y_1546_ = v_a_1513_;
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v_dummy_1547_; lean_object* v_nargs_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_dummy_1547_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1548_ = l_Lean_Expr_getAppNumArgs(v_a_1518_);
lean_inc(v_nargs_1548_);
v___x_1549_ = lean_mk_array(v_nargs_1548_, v_dummy_1547_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_sub(v_nargs_1548_, v___x_1550_);
lean_dec(v_nargs_1548_);
lean_inc(v_a_1518_);
v___x_1552_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1518_, v___x_1549_, v___x_1551_);
v___x_1553_ = lean_nat_add(v_numParams_1536_, v_numIndices_1537_);
lean_dec(v_numIndices_1537_);
v___x_1554_ = lean_array_get_size(v___x_1552_);
v___x_1555_ = lean_nat_dec_eq(v___x_1553_, v___x_1554_);
lean_dec(v___x_1553_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v___x_1552_);
lean_dec_ref(v_val_1541_);
lean_dec(v_numParams_1536_);
lean_dec(v_us_1521_);
v___x_1556_ = lean_box(0);
v___x_1557_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1556_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
return v___x_1557_;
}
else
{
lean_object* v_toConstantVal_1558_; lean_object* v_name_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_toConstantVal_1558_ = lean_ctor_get(v_val_1541_, 0);
lean_inc_ref(v_toConstantVal_1558_);
lean_dec_ref(v_val_1541_);
v_name_1559_ = lean_ctor_get(v_toConstantVal_1558_, 0);
lean_inc(v_name_1559_);
lean_dec_ref(v_toConstantVal_1558_);
v___x_1560_ = l_Lean_mkConst(v_name_1559_, v_us_1521_);
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = l_Array_toSubarray___redArg(v___x_1552_, v___x_1561_, v_numParams_1536_);
v___x_1563_ = l_Subarray_copy___redArg(v___x_1562_);
v___x_1564_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1560_, v___x_1563_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec_ref(v___x_1563_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
lean_inc(v_a_1518_);
lean_inc_ref(v_e_1509_);
lean_inc(v_structName_1507_);
lean_inc(v_idx_1508_);
v___x_1566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1508_, v_structName_1507_, v_e_1509_, v_idx_1508_, v_a_1518_, v___x_1561_, v_a_1565_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
v___x_1568_ = lean_whnf(v_a_1567_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1580_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1580_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1580_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
if (lean_obj_tag(v_a_1569_) == 7)
{
lean_object* v_binderType_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
lean_dec(v_a_1518_);
lean_dec_ref(v_e_1509_);
lean_dec(v_idx_1508_);
lean_dec(v_structName_1507_);
v_binderType_1573_ = lean_ctor_get(v_a_1569_, 1);
lean_inc_ref(v_binderType_1573_);
lean_dec_ref_known(v_a_1569_, 3);
v___x_1574_ = lean_expr_consume_type_annotations(v_binderType_1573_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1571_);
lean_dec(v_a_1569_);
v___x_1578_ = lean_box(0);
v___x_1579_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1578_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
return v___x_1579_;
}
}
}
else
{
lean_dec(v_a_1518_);
lean_dec_ref(v_e_1509_);
lean_dec(v_idx_1508_);
lean_dec(v_structName_1507_);
return v___x_1568_;
}
}
else
{
lean_dec(v_a_1518_);
lean_dec_ref(v_e_1509_);
lean_dec(v_idx_1508_);
lean_dec(v_structName_1507_);
return v___x_1566_;
}
}
else
{
lean_dec(v_a_1518_);
lean_dec_ref(v_e_1509_);
lean_dec(v_idx_1508_);
lean_dec(v_structName_1507_);
return v___x_1564_;
}
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_a_1540_);
lean_dec(v_numIndices_1537_);
lean_dec(v_numParams_1536_);
lean_dec_ref(v_toConstantVal_1535_);
lean_dec(v_us_1521_);
v___x_1593_ = lean_box(0);
v___x_1594_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1593_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1594_;
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_numIndices_1537_);
lean_dec(v_numParams_1536_);
lean_dec_ref(v_toConstantVal_1535_);
lean_dec(v_us_1521_);
lean_dec(v_a_1518_);
lean_dec_ref(v_e_1509_);
lean_dec(v_idx_1508_);
lean_dec(v_structName_1507_);
v_a_1595_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1539_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1539_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1533_, 2);
lean_dec_ref(v_val_1532_);
lean_dec(v_us_1521_);
goto v___jp_1523_;
}
}
else
{
lean_dec(v_ctors_1533_);
lean_dec_ref(v_val_1532_);
lean_dec(v_us_1521_);
goto v___jp_1523_;
}
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_val_1531_);
lean_dec(v_us_1521_);
v___x_1603_ = lean_box(0);
v___x_1604_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1603_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1604_;
}
}
v___jp_1523_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_box(0);
v___x_1525_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1524_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1525_;
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec_ref(v___x_1519_);
v___x_1605_ = lean_box(0);
v___x_1606_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1507_, v_idx_1508_, v_e_1509_, v_a_1518_, lean_box(0), v___x_1605_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1606_;
}
}
else
{
lean_dec_ref(v_e_1509_);
lean_dec(v_idx_1508_);
lean_dec(v_structName_1507_);
return v___x_1517_;
}
}
else
{
lean_dec_ref(v_e_1509_);
lean_dec(v_idx_1508_);
lean_dec(v_structName_1507_);
return v___x_1515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1607_, lean_object* v_idx_1608_, lean_object* v_e_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1607_, v_idx_1608_, v_e_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1616_, lean_object* v_structName_1617_, lean_object* v_e_1618_, lean_object* v_idx_1619_, lean_object* v_a_1620_, lean_object* v_inst_1621_, lean_object* v_R_1622_, lean_object* v_a_1623_, lean_object* v_b_1624_, lean_object* v_c_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1616_, v_structName_1617_, v_e_1618_, v_idx_1619_, v_a_1620_, v_a_1623_, v_b_1624_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1632_, lean_object* v_structName_1633_, lean_object* v_e_1634_, lean_object* v_idx_1635_, lean_object* v_a_1636_, lean_object* v_inst_1637_, lean_object* v_R_1638_, lean_object* v_a_1639_, lean_object* v_b_1640_, lean_object* v_c_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1632_, v_structName_1633_, v_e_1634_, v_idx_1635_, v_a_1636_, v_inst_1637_, v_R_1638_, v_a_1639_, v_b_1640_, v_c_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v_upperBound_1632_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1648_, lean_object* v_structName_1649_, lean_object* v_e_1650_, lean_object* v_idx_1651_, lean_object* v_a_1652_, lean_object* v_inst_1653_, lean_object* v_R_1654_, lean_object* v_a_1655_, lean_object* v_b_1656_, lean_object* v_c_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1648_, v_structName_1649_, v_e_1650_, v_idx_1651_, v_a_1652_, v_a_1655_, v_b_1656_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1664_, lean_object* v_structName_1665_, lean_object* v_e_1666_, lean_object* v_idx_1667_, lean_object* v_a_1668_, lean_object* v_inst_1669_, lean_object* v_R_1670_, lean_object* v_a_1671_, lean_object* v_b_1672_, lean_object* v_c_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1664_, v_structName_1665_, v_e_1666_, v_idx_1667_, v_a_1668_, v_inst_1669_, v_R_1670_, v_a_1671_, v_b_1672_, v_c_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v_upperBound_1664_);
return v_res_1679_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1689_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1690_ = l_Lean_indentExpr(v_type_1683_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1691_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1700_, lean_object* v_type_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_type_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1708_, v_type_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v_ks_1720_; lean_object* v_vs_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1745_; 
v_ks_1720_ = lean_ctor_get(v_x_1716_, 0);
v_vs_1721_ = lean_ctor_get(v_x_1716_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_x_1716_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1723_ = v_x_1716_;
v_isShared_1724_ = v_isSharedCheck_1745_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_vs_1721_);
lean_inc(v_ks_1720_);
lean_dec(v_x_1716_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1745_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = lean_array_get_size(v_ks_1720_);
v___x_1726_ = lean_nat_dec_lt(v_x_1717_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec(v_x_1717_);
v___x_1727_ = lean_array_push(v_ks_1720_, v_x_1718_);
v___x_1728_ = lean_array_push(v_vs_1721_, v_x_1719_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1728_);
lean_ctor_set(v___x_1723_, 0, v___x_1727_);
v___x_1730_ = v___x_1723_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
else
{
lean_object* v_k_x27_1732_; uint8_t v___x_1733_; 
v_k_x27_1732_ = lean_array_fget_borrowed(v_ks_1720_, v_x_1717_);
v___x_1733_ = l_Lean_instBEqMVarId_beq(v_x_1718_, v_k_x27_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1735_; 
if (v_isShared_1724_ == 0)
{
v___x_1735_ = v___x_1723_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_ks_1720_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_vs_1721_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_x_1717_, v___x_1736_);
lean_dec(v_x_1717_);
v_x_1716_ = v___x_1735_;
v_x_1717_ = v___x_1737_;
goto _start;
}
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1740_ = lean_array_fset(v_ks_1720_, v_x_1717_, v_x_1718_);
v___x_1741_ = lean_array_fset(v_vs_1721_, v_x_1717_, v_x_1719_);
lean_dec(v_x_1717_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1741_);
lean_ctor_set(v___x_1723_, 0, v___x_1740_);
v___x_1743_ = v___x_1723_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1746_, lean_object* v_k_1747_, lean_object* v_v_1748_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1746_, v___x_1749_, v_k_1747_, v_v_1748_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1752_, size_t v_x_1753_, size_t v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v_es_1757_; size_t v___x_1758_; size_t v___x_1759_; lean_object* v_j_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_es_1757_ = lean_ctor_get(v_x_1752_, 0);
v___x_1758_ = ((size_t)31ULL);
v___x_1759_ = lean_usize_land(v_x_1753_, v___x_1758_);
v_j_1760_ = lean_usize_to_nat(v___x_1759_);
v___x_1761_ = lean_array_get_size(v_es_1757_);
v___x_1762_ = lean_nat_dec_lt(v_j_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_dec(v_j_1760_);
lean_dec(v_x_1756_);
lean_dec(v_x_1755_);
return v_x_1752_;
}
else
{
lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1801_; 
lean_inc_ref(v_es_1757_);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_x_1752_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v_x_1752_, 0);
lean_dec(v_unused_1802_);
v___x_1764_ = v_x_1752_;
v_isShared_1765_ = v_isSharedCheck_1801_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v_x_1752_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1801_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_v_1766_; lean_object* v___x_1767_; lean_object* v_xs_x27_1768_; lean_object* v___y_1770_; 
v_v_1766_ = lean_array_fget(v_es_1757_, v_j_1760_);
v___x_1767_ = lean_box(0);
v_xs_x27_1768_ = lean_array_fset(v_es_1757_, v_j_1760_, v___x_1767_);
switch(lean_obj_tag(v_v_1766_))
{
case 0:
{
lean_object* v_key_1775_; lean_object* v_val_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1786_; 
v_key_1775_ = lean_ctor_get(v_v_1766_, 0);
v_val_1776_ = lean_ctor_get(v_v_1766_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_v_1766_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1778_ = v_v_1766_;
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_val_1776_);
lean_inc(v_key_1775_);
lean_dec(v_v_1766_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
uint8_t v___x_1780_; 
v___x_1780_ = l_Lean_instBEqMVarId_beq(v_x_1755_, v_key_1775_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_del_object(v___x_1778_);
v___x_1781_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1775_, v_val_1776_, v_x_1755_, v_x_1756_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
v___y_1770_ = v___x_1782_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1784_; 
lean_dec(v_val_1776_);
lean_dec(v_key_1775_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 1, v_x_1756_);
lean_ctor_set(v___x_1778_, 0, v_x_1755_);
v___x_1784_ = v___x_1778_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_x_1755_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_x_1756_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
v___y_1770_ = v___x_1784_;
goto v___jp_1769_;
}
}
}
}
case 1:
{
lean_object* v_node_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1799_; 
v_node_1787_ = lean_ctor_get(v_v_1766_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_v_1766_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1789_ = v_v_1766_;
v_isShared_1790_ = v_isSharedCheck_1799_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_node_1787_);
lean_dec(v_v_1766_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1799_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
size_t v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1791_ = ((size_t)5ULL);
v___x_1792_ = lean_usize_shift_right(v_x_1753_, v___x_1791_);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_x_1754_, v___x_1793_);
v___x_1795_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1787_, v___x_1792_, v___x_1794_, v_x_1755_, v_x_1756_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1795_);
v___x_1797_ = v___x_1789_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
v___y_1770_ = v___x_1797_;
goto v___jp_1769_;
}
}
}
default: 
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v_x_1755_);
lean_ctor_set(v___x_1800_, 1, v_x_1756_);
v___y_1770_ = v___x_1800_;
goto v___jp_1769_;
}
}
v___jp_1769_:
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = lean_array_fset(v_xs_x27_1768_, v_j_1760_, v___y_1770_);
lean_dec(v_j_1760_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1771_);
v___x_1773_ = v___x_1764_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
else
{
lean_object* v_ks_1803_; lean_object* v_vs_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1822_; 
v_ks_1803_ = lean_ctor_get(v_x_1752_, 0);
v_vs_1804_ = lean_ctor_get(v_x_1752_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_x_1752_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1806_ = v_x_1752_;
v_isShared_1807_ = v_isSharedCheck_1822_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_vs_1804_);
lean_inc(v_ks_1803_);
lean_dec(v_x_1752_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1822_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_ks_1803_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_vs_1804_);
v___x_1809_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v_newNode_1810_; size_t v___x_1811_; uint8_t v___x_1812_; 
v_newNode_1810_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1809_, v_x_1755_, v_x_1756_);
v___x_1811_ = ((size_t)7ULL);
v___x_1812_ = lean_usize_dec_le(v___x_1811_, v_x_1754_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1813_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1810_);
v___x_1814_ = lean_unsigned_to_nat(4u);
v___x_1815_ = lean_nat_dec_lt(v___x_1813_, v___x_1814_);
lean_dec(v___x_1813_);
if (v___x_1815_ == 0)
{
lean_object* v_ks_1816_; lean_object* v_vs_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_ks_1816_ = lean_ctor_get(v_newNode_1810_, 0);
lean_inc_ref(v_ks_1816_);
v_vs_1817_ = lean_ctor_get(v_newNode_1810_, 1);
lean_inc_ref(v_vs_1817_);
lean_dec_ref(v_newNode_1810_);
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1820_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1754_, v_ks_1816_, v_vs_1817_, v___x_1818_, v___x_1819_);
lean_dec_ref(v_vs_1817_);
lean_dec_ref(v_ks_1816_);
return v___x_1820_;
}
else
{
return v_newNode_1810_;
}
}
else
{
return v_newNode_1810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1823_, lean_object* v_keys_1824_, lean_object* v_vals_1825_, lean_object* v_i_1826_, lean_object* v_entries_1827_){
_start:
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = lean_array_get_size(v_keys_1824_);
v___x_1829_ = lean_nat_dec_lt(v_i_1826_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_dec(v_i_1826_);
return v_entries_1827_;
}
else
{
lean_object* v_k_1830_; lean_object* v_v_1831_; uint64_t v___x_1832_; size_t v_h_1833_; size_t v___x_1834_; lean_object* v___x_1835_; size_t v___x_1836_; size_t v___x_1837_; size_t v___x_1838_; size_t v_h_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_k_1830_ = lean_array_fget_borrowed(v_keys_1824_, v_i_1826_);
v_v_1831_ = lean_array_fget_borrowed(v_vals_1825_, v_i_1826_);
v___x_1832_ = l_Lean_instHashableMVarId_hash(v_k_1830_);
v_h_1833_ = lean_uint64_to_usize(v___x_1832_);
v___x_1834_ = ((size_t)5ULL);
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_sub(v_depth_1823_, v___x_1836_);
v___x_1838_ = lean_usize_mul(v___x_1834_, v___x_1837_);
v_h_1839_ = lean_usize_shift_right(v_h_1833_, v___x_1838_);
v___x_1840_ = lean_nat_add(v_i_1826_, v___x_1835_);
lean_dec(v_i_1826_);
lean_inc(v_v_1831_);
lean_inc(v_k_1830_);
v___x_1841_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1827_, v_h_1839_, v_depth_1823_, v_k_1830_, v_v_1831_);
v_i_1826_ = v___x_1840_;
v_entries_1827_ = v___x_1841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1843_, lean_object* v_keys_1844_, lean_object* v_vals_1845_, lean_object* v_i_1846_, lean_object* v_entries_1847_){
_start:
{
size_t v_depth_boxed_1848_; lean_object* v_res_1849_; 
v_depth_boxed_1848_ = lean_unbox_usize(v_depth_1843_);
lean_dec(v_depth_1843_);
v_res_1849_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1848_, v_keys_1844_, v_vals_1845_, v_i_1846_, v_entries_1847_);
lean_dec_ref(v_vals_1845_);
lean_dec_ref(v_keys_1844_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_){
_start:
{
size_t v_x_1155__boxed_1855_; size_t v_x_1156__boxed_1856_; lean_object* v_res_1857_; 
v_x_1155__boxed_1855_ = lean_unbox_usize(v_x_1851_);
lean_dec(v_x_1851_);
v_x_1156__boxed_1856_ = lean_unbox_usize(v_x_1852_);
lean_dec(v_x_1852_);
v_res_1857_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1850_, v_x_1155__boxed_1855_, v_x_1156__boxed_1856_, v_x_1853_, v_x_1854_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
uint64_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; lean_object* v___x_1864_; 
v___x_1861_ = l_Lean_instHashableMVarId_hash(v_x_1859_);
v___x_1862_ = lean_uint64_to_usize(v___x_1861_);
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1858_, v___x_1862_, v___x_1863_, v_x_1859_, v_x_1860_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1865_, lean_object* v_val_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v_mctx_1870_; lean_object* v_cache_1871_; lean_object* v_zetaDeltaFVarIds_1872_; lean_object* v_postponed_1873_; lean_object* v_diag_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1904_; 
v___x_1869_ = lean_st_ref_take(v___y_1867_);
v_mctx_1870_ = lean_ctor_get(v___x_1869_, 0);
v_cache_1871_ = lean_ctor_get(v___x_1869_, 1);
v_zetaDeltaFVarIds_1872_ = lean_ctor_get(v___x_1869_, 2);
v_postponed_1873_ = lean_ctor_get(v___x_1869_, 3);
v_diag_1874_ = lean_ctor_get(v___x_1869_, 4);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1876_ = v___x_1869_;
v_isShared_1877_ = v_isSharedCheck_1904_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_diag_1874_);
lean_inc(v_postponed_1873_);
lean_inc(v_zetaDeltaFVarIds_1872_);
lean_inc(v_cache_1871_);
lean_inc(v_mctx_1870_);
lean_dec(v___x_1869_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1904_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_depth_1878_; lean_object* v_levelAssignDepth_1879_; lean_object* v_lmvarCounter_1880_; lean_object* v_mvarCounter_1881_; lean_object* v_lDecls_1882_; lean_object* v_decls_1883_; lean_object* v_userNames_1884_; lean_object* v_lAssignment_1885_; lean_object* v_eAssignment_1886_; lean_object* v_dAssignment_1887_; lean_object* v_instanceTypedMVars_1888_; lean_object* v_synthNormMemo_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1903_; 
v_depth_1878_ = lean_ctor_get(v_mctx_1870_, 0);
v_levelAssignDepth_1879_ = lean_ctor_get(v_mctx_1870_, 1);
v_lmvarCounter_1880_ = lean_ctor_get(v_mctx_1870_, 2);
v_mvarCounter_1881_ = lean_ctor_get(v_mctx_1870_, 3);
v_lDecls_1882_ = lean_ctor_get(v_mctx_1870_, 4);
v_decls_1883_ = lean_ctor_get(v_mctx_1870_, 5);
v_userNames_1884_ = lean_ctor_get(v_mctx_1870_, 6);
v_lAssignment_1885_ = lean_ctor_get(v_mctx_1870_, 7);
v_eAssignment_1886_ = lean_ctor_get(v_mctx_1870_, 8);
v_dAssignment_1887_ = lean_ctor_get(v_mctx_1870_, 9);
v_instanceTypedMVars_1888_ = lean_ctor_get(v_mctx_1870_, 10);
v_synthNormMemo_1889_ = lean_ctor_get(v_mctx_1870_, 11);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_mctx_1870_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1891_ = v_mctx_1870_;
v_isShared_1892_ = v_isSharedCheck_1903_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_synthNormMemo_1889_);
lean_inc(v_instanceTypedMVars_1888_);
lean_inc(v_dAssignment_1887_);
lean_inc(v_eAssignment_1886_);
lean_inc(v_lAssignment_1885_);
lean_inc(v_userNames_1884_);
lean_inc(v_decls_1883_);
lean_inc(v_lDecls_1882_);
lean_inc(v_mvarCounter_1881_);
lean_inc(v_lmvarCounter_1880_);
lean_inc(v_levelAssignDepth_1879_);
lean_inc(v_depth_1878_);
lean_dec(v_mctx_1870_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1903_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1886_, v_mvarId_1865_, v_val_1866_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 8, v___x_1894_);
v___x_1896_ = v___x_1891_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_depth_1878_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_levelAssignDepth_1879_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_lmvarCounter_1880_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_mvarCounter_1881_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_lDecls_1882_);
lean_ctor_set(v_reuseFailAlloc_1902_, 5, v_decls_1883_);
lean_ctor_set(v_reuseFailAlloc_1902_, 6, v_userNames_1884_);
lean_ctor_set(v_reuseFailAlloc_1902_, 7, v_lAssignment_1885_);
lean_ctor_set(v_reuseFailAlloc_1902_, 8, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1902_, 9, v_dAssignment_1887_);
lean_ctor_set(v_reuseFailAlloc_1902_, 10, v_instanceTypedMVars_1888_);
lean_ctor_set(v_reuseFailAlloc_1902_, 11, v_synthNormMemo_1889_);
v___x_1896_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1896_);
v___x_1898_ = v___x_1876_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_cache_1871_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_zetaDeltaFVarIds_1872_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_postponed_1873_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_diag_1874_);
v___x_1898_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_st_ref_put(v___y_1867_, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1893_);
return v___x_1900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1905_, lean_object* v_val_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1905_, v_val_1906_, v___y_1907_);
lean_dec(v___y_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v___x_1916_; 
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc_ref(v_type_1910_);
v___x_1916_ = lean_infer_type(v_type_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1918_ = l_Lean_Meta_whnfD(v_a_1917_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1953_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
switch(lean_obj_tag(v_a_1919_))
{
case 3:
{
lean_object* v_u_1923_; lean_object* v___x_1925_; 
lean_dec_ref(v_type_1910_);
v_u_1923_ = lean_ctor_get(v_a_1919_, 0);
lean_inc(v_u_1923_);
lean_dec_ref_known(v_a_1919_, 1);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_u_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_u_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
case 2:
{
lean_object* v_mvarId_1927_; lean_object* v___x_1928_; 
lean_del_object(v___x_1921_);
v_mvarId_1927_ = lean_ctor_get(v_a_1919_, 0);
lean_inc_n(v_mvarId_1927_, 2);
lean_dec_ref_known(v_a_1919_, 1);
v___x_1928_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1927_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; uint8_t v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec_ref(v_type_1910_);
v___x_1931_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc_n(v_a_1932_, 2);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_mkSort(v_a_1932_);
v___x_1934_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1927_, v___x_1933_, v_a_1912_);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1934_, 0);
lean_dec(v_unused_1942_);
v___x_1936_ = v___x_1934_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_dec(v___x_1934_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_a_1932_);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1932_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_dec(v_mvarId_1927_);
return v___x_1931_;
}
}
else
{
lean_object* v___x_1943_; 
lean_dec(v_mvarId_1927_);
v___x_1943_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_1943_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_mvarId_1927_);
lean_dec_ref(v_type_1910_);
v_a_1944_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1928_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1928_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
default: 
{
lean_object* v___x_1952_; 
lean_del_object(v___x_1921_);
lean_dec(v_a_1919_);
v___x_1952_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_type_1910_);
v_a_1954_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1918_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1918_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_type_1910_);
v_a_1962_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1916_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1916_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Meta_getLevel(v_type_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1977_, lean_object* v_val_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1977_, v_val_1978_, v___y_1980_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1985_, lean_object* v_val_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1985_, v_val_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1994_, v_x_1995_, v_x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1998_, lean_object* v_x_1999_, size_t v_x_2000_, size_t v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1999_, v_x_2000_, v_x_2001_, v_x_2002_, v_x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
size_t v_x_1504__boxed_2011_; size_t v_x_1505__boxed_2012_; lean_object* v_res_2013_; 
v_x_1504__boxed_2011_ = lean_unbox_usize(v_x_2007_);
lean_dec(v_x_2007_);
v_x_1505__boxed_2012_ = lean_unbox_usize(v_x_2008_);
lean_dec(v_x_2008_);
v_res_2013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2005_, v_x_2006_, v_x_1504__boxed_2011_, v_x_1505__boxed_2012_, v_x_2009_, v_x_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2014_, lean_object* v_n_2015_, lean_object* v_k_2016_, lean_object* v_v_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2015_, v_k_2016_, v_v_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2019_, size_t v_depth_2020_, lean_object* v_keys_2021_, lean_object* v_vals_2022_, lean_object* v_heq_2023_, lean_object* v_i_2024_, lean_object* v_entries_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2020_, v_keys_2021_, v_vals_2022_, v_i_2024_, v_entries_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2027_, lean_object* v_depth_2028_, lean_object* v_keys_2029_, lean_object* v_vals_2030_, lean_object* v_heq_2031_, lean_object* v_i_2032_, lean_object* v_entries_2033_){
_start:
{
size_t v_depth_boxed_2034_; lean_object* v_res_2035_; 
v_depth_boxed_2034_ = lean_unbox_usize(v_depth_2028_);
lean_dec(v_depth_2028_);
v_res_2035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2027_, v_depth_boxed_2034_, v_keys_2029_, v_vals_2030_, v_heq_2031_, v_i_2032_, v_entries_2033_);
lean_dec_ref(v_vals_2030_);
lean_dec_ref(v_keys_2029_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2037_, v_x_2038_, v_x_2039_, v_x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2042_, lean_object* v_b_2043_, lean_object* v_c_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
v___x_2050_ = lean_apply_7(v_k_2042_, v_b_2043_, v_c_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, lean_box(0));
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2051_, lean_object* v_b_2052_, lean_object* v_c_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2051_, v_b_2052_, v_c_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2060_, lean_object* v_k_2061_, uint8_t v_cleanupAnnotations_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___f_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2068_, 0, v_k_2061_);
v___x_2069_ = 0;
v___x_2070_ = lean_box(0);
v___x_2071_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2069_, v___x_2070_, v_type_2060_, v___f_2068_, v_cleanupAnnotations_2062_, v___x_2069_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2071_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2071_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2088_, lean_object* v_k_2089_, lean_object* v_cleanupAnnotations_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2096_; lean_object* v_res_2097_; 
v_cleanupAnnotations_boxed_2096_ = lean_unbox(v_cleanupAnnotations_2090_);
v_res_2097_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2088_, v_k_2089_, v_cleanupAnnotations_boxed_2096_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2098_, lean_object* v_type_2099_, lean_object* v_k_2100_, uint8_t v_cleanupAnnotations_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2099_, v_k_2100_, v_cleanupAnnotations_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_type_2109_, lean_object* v_k_2110_, lean_object* v_cleanupAnnotations_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2117_; lean_object* v_res_2118_; 
v_cleanupAnnotations_boxed_2117_ = lean_unbox(v_cleanupAnnotations_2111_);
v_res_2118_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2108_, v_type_2109_, v_k_2110_, v_cleanupAnnotations_boxed_2117_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2119_, size_t v_i_2120_, size_t v_stop_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
uint8_t v___x_2128_; 
v___x_2128_ = lean_usize_dec_eq(v_i_2120_, v_stop_2121_);
if (v___x_2128_ == 0)
{
size_t v___x_2129_; size_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = ((size_t)1ULL);
v___x_2130_ = lean_usize_sub(v_i_2120_, v___x_2129_);
v___x_2131_ = lean_array_uget_borrowed(v_as_2119_, v___x_2130_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
lean_inc(v___y_2124_);
lean_inc_ref(v___y_2123_);
lean_inc(v___x_2131_);
v___x_2132_ = lean_infer_type(v___x_2131_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l_Lean_Meta_getLevel(v_a_2133_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = l_Lean_mkLevelIMax_x27(v_a_2135_, v_b_2122_);
v_i_2120_ = v___x_2130_;
v_b_2122_ = v___x_2136_;
goto _start;
}
else
{
lean_dec(v_b_2122_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2134_, 1);
v_i_2120_ = v___x_2130_;
v_b_2122_ = v_a_2138_;
goto _start;
}
else
{
return v___x_2134_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_b_2122_);
v_a_2140_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2132_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2132_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_b_2122_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2149_, lean_object* v_i_2150_, lean_object* v_stop_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
size_t v_i_boxed_2158_; size_t v_stop_boxed_2159_; lean_object* v_res_2160_; 
v_i_boxed_2158_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_stop_boxed_2159_ = lean_unbox_usize(v_stop_2151_);
lean_dec(v_stop_2151_);
v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2149_, v_i_boxed_2158_, v_stop_boxed_2159_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_as_2149_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2161_, lean_object* v_e_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___y_2169_; lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Meta_getLevel(v_e_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v___x_2190_ = lean_array_get_size(v_xs_2161_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_nat_dec_lt(v___x_2191_, v___x_2190_);
if (v___x_2192_ == 0)
{
v___y_2169_ = v___x_2188_;
goto v___jp_2168_;
}
else
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2193_ = lean_usize_of_nat(v___x_2190_);
v___x_2194_ = ((size_t)0ULL);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2161_, v___x_2193_, v___x_2194_, v_a_2189_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
v___y_2169_ = v___x_2195_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_a_2196_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2188_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2188_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
v___jp_2168_:
{
if (lean_obj_tag(v___y_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2179_; 
v_a_2170_ = lean_ctor_get(v___y_2169_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___y_2169_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2172_ = v___y_2169_;
v_isShared_2173_ = v_isSharedCheck_2179_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___y_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2179_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2174_ = l_Lean_Level_normalize(v_a_2170_);
lean_dec(v_a_2170_);
v___x_2175_ = l_Lean_mkSort(v___x_2174_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2175_);
v___x_2177_ = v___x_2172_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___y_2169_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___y_2169_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___y_2169_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___y_2169_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2204_, lean_object* v_e_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2204_, v_e_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec_ref(v_xs_2204_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___f_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; 
v___f_2219_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2220_ = 0;
v___x_2221_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2213_, v___f_2219_, v___x_2220_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2229_, lean_object* v_k_2230_, uint8_t v_cleanupAnnotations_2231_, uint8_t v_preserveNondepLet_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___f_2238_; uint8_t v___x_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2238_, 0, v_k_2230_);
v___x_2239_ = 1;
v___x_2240_ = 0;
v___x_2241_ = lean_box(0);
v___x_2242_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2229_, v___x_2239_, v___x_2239_, v_preserveNondepLet_2232_, v___x_2240_, v___x_2241_, v___f_2238_, v_cleanupAnnotations_2231_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2242_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2242_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2259_, lean_object* v_k_2260_, lean_object* v_cleanupAnnotations_2261_, lean_object* v_preserveNondepLet_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2268_; uint8_t v_preserveNondepLet_boxed_2269_; lean_object* v_res_2270_; 
v_cleanupAnnotations_boxed_2268_ = lean_unbox(v_cleanupAnnotations_2261_);
v_preserveNondepLet_boxed_2269_ = lean_unbox(v_preserveNondepLet_2262_);
v_res_2270_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2259_, v_k_2260_, v_cleanupAnnotations_boxed_2268_, v_preserveNondepLet_boxed_2269_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2271_, lean_object* v_e_2272_, lean_object* v_k_2273_, uint8_t v_cleanupAnnotations_2274_, uint8_t v_preserveNondepLet_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2272_, v_k_2273_, v_cleanupAnnotations_2274_, v_preserveNondepLet_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_e_2283_, lean_object* v_k_2284_, lean_object* v_cleanupAnnotations_2285_, lean_object* v_preserveNondepLet_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2292_; uint8_t v_preserveNondepLet_boxed_2293_; lean_object* v_res_2294_; 
v_cleanupAnnotations_boxed_2292_ = lean_unbox(v_cleanupAnnotations_2285_);
v_preserveNondepLet_boxed_2293_ = lean_unbox(v_preserveNondepLet_2286_);
v_res_2294_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2282_, v_e_2283_, v_k_2284_, v_cleanupAnnotations_boxed_2292_, v_preserveNondepLet_boxed_2293_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2295_, lean_object* v_e_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___x_2302_; 
lean_inc(v___y_2300_);
lean_inc_ref(v___y_2299_);
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
v___x_2302_ = lean_infer_type(v_e_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; uint8_t v___x_2304_; uint8_t v___x_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = 0;
v___x_2305_ = 1;
v___x_2306_ = 1;
v___x_2307_ = l_Lean_Meta_mkForallFVars(v_xs_2295_, v_a_2303_, v___x_2304_, v___x_2305_, v___x_2304_, v___x_2306_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
return v___x_2307_;
}
else
{
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2308_, lean_object* v_e_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2308_, v_e_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec_ref(v_xs_2308_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___f_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v___f_2323_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2324_ = 0;
v___x_2325_ = 1;
v___x_2326_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2317_, v___f_2323_, v___x_2324_, v___x_2325_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
return v_res_2333_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2346_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2347_ = l_Lean_MessageData_ofName(v_mvarId_2340_);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2350_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2359_, lean_object* v_mvarId_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_mvarId_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2367_, v_mvarId_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v_mctx_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_st_ref_get(v_a_2377_);
v_mctx_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc_ref(v_mctx_2382_);
lean_dec(v___x_2381_);
v___x_2383_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2382_, v_mvarId_2375_);
lean_dec_ref(v_mctx_2382_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
return v___x_2384_;
}
else
{
lean_object* v_val_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_mvarId_2375_);
v_val_2385_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2387_ = v___x_2383_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_val_2385_);
lean_dec(v___x_2383_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_type_2389_; lean_object* v___x_2391_; 
v_type_2389_ = lean_ctor_get(v_val_2385_, 2);
lean_inc_ref(v_type_2389_);
lean_dec(v_val_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 0);
lean_ctor_set(v___x_2387_, 0, v_type_2389_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_type_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_lctx_2406_; lean_object* v___x_2407_; 
v_lctx_2406_ = lean_ctor_get(v_a_2402_, 2);
lean_inc(v_fvarId_2401_);
lean_inc_ref(v_lctx_2406_);
v___x_2407_ = lean_local_ctx_find(v_lctx_2406_, v_fvarId_2401_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2401_, v_a_2403_, v_a_2404_);
return v___x_2408_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_fvarId_2401_);
v_val_2409_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2411_ = v___x_2407_;
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v___x_2407_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = l_Lean_LocalDecl_type(v_val_2409_);
lean_dec(v_val_2409_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec_ref(v_a_2419_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2424_, v_a_2425_, v_a_2427_, v_a_2428_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
return v_res_2437_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_instMonadEIO___redArg();
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2440_ = l_StateRefT_x27_instMonad___redArg(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_instMonadExceptOfEIO___redArg();
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___f_2445_; 
v___x_2444_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2445_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2445_, 0, v___x_2444_);
return v___f_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___f_2447_; 
v___x_2446_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2447_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2447_, 0, v___x_2446_);
return v___f_2447_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; 
v___f_2448_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___f_2449_);
lean_ctor_set(v___x_2450_, 1, v___f_2448_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___f_2452_; 
v___x_2451_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2452_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2452_, 0, v___x_2451_);
return v___f_2452_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___f_2454_; 
v___x_2453_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2454_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2454_, 0, v___x_2453_);
return v___f_2454_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; 
v___f_2455_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2456_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___f_2456_);
lean_ctor_set(v___x_2457_, 1, v___f_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2460_, lean_object* v_inferType_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
uint8_t v_cacheInferType_2506_; 
v_cacheInferType_2506_ = lean_ctor_get_uint8(v_a_2462_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2506_ == 0)
{
lean_dec_ref(v_e_2460_);
goto v___jp_2467_;
}
else
{
uint8_t v___x_2507_; 
v___x_2507_ = l_Lean_Expr_hasMVar(v_e_2460_);
if (v___x_2507_ == 0)
{
lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___f_2508_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2509_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2510_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2460_, v_a_2462_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2608_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2608_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2608_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2555_; lean_object* v_cache_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2603_; 
v___x_2555_ = lean_st_ref_get(v_a_2463_);
v_cache_2556_ = lean_ctor_get(v___x_2555_, 1);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; lean_object* v_unused_2605_; lean_object* v_unused_2606_; lean_object* v_unused_2607_; 
v_unused_2604_ = lean_ctor_get(v___x_2555_, 4);
lean_dec(v_unused_2604_);
v_unused_2605_ = lean_ctor_get(v___x_2555_, 3);
lean_dec(v_unused_2605_);
v_unused_2606_ = lean_ctor_get(v___x_2555_, 2);
lean_dec(v_unused_2606_);
v_unused_2607_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2607_);
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2603_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_cache_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2603_;
goto v_resetjp_2557_;
}
v___jp_2515_:
{
lean_object* v___x_2516_; 
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2516_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; uint8_t v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
v___x_2518_ = l_Lean_Expr_hasMVar(v_a_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2553_; 
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___x_2516_, 0);
lean_dec(v_unused_2554_);
v___x_2520_ = v___x_2516_;
v_isShared_2521_ = v_isSharedCheck_2553_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v___x_2516_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2553_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v_cache_2523_; lean_object* v_mctx_2524_; lean_object* v_zetaDeltaFVarIds_2525_; lean_object* v_postponed_2526_; lean_object* v_diag_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2552_; 
v___x_2522_ = lean_st_ref_take(v_a_2463_);
v_cache_2523_ = lean_ctor_get(v___x_2522_, 1);
v_mctx_2524_ = lean_ctor_get(v___x_2522_, 0);
v_zetaDeltaFVarIds_2525_ = lean_ctor_get(v___x_2522_, 2);
v_postponed_2526_ = lean_ctor_get(v___x_2522_, 3);
v_diag_2527_ = lean_ctor_get(v___x_2522_, 4);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2529_ = v___x_2522_;
v_isShared_2530_ = v_isSharedCheck_2552_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_diag_2527_);
lean_inc(v_postponed_2526_);
lean_inc(v_zetaDeltaFVarIds_2525_);
lean_inc(v_cache_2523_);
lean_inc(v_mctx_2524_);
lean_dec(v___x_2522_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2552_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v_inferType_2531_; lean_object* v_funInfo_2532_; lean_object* v_synthInstance_2533_; lean_object* v_whnf_2534_; lean_object* v_defEqTrans_2535_; lean_object* v_defEqPerm_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2551_; 
v_inferType_2531_ = lean_ctor_get(v_cache_2523_, 0);
v_funInfo_2532_ = lean_ctor_get(v_cache_2523_, 1);
v_synthInstance_2533_ = lean_ctor_get(v_cache_2523_, 2);
v_whnf_2534_ = lean_ctor_get(v_cache_2523_, 3);
v_defEqTrans_2535_ = lean_ctor_get(v_cache_2523_, 4);
v_defEqPerm_2536_ = lean_ctor_get(v_cache_2523_, 5);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_cache_2523_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2538_ = v_cache_2523_;
v_isShared_2539_ = v_isSharedCheck_2551_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_defEqPerm_2536_);
lean_inc(v_defEqTrans_2535_);
lean_inc(v_whnf_2534_);
lean_inc(v_synthInstance_2533_);
lean_inc(v_funInfo_2532_);
lean_inc(v_inferType_2531_);
lean_dec(v_cache_2523_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2551_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_inc(v_a_2517_);
v___x_2540_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2508_, v___x_2509_, v_inferType_2531_, v_a_2511_, v_a_2517_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_funInfo_2532_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_synthInstance_2533_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v_whnf_2534_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v_defEqTrans_2535_);
lean_ctor_set(v_reuseFailAlloc_2550_, 5, v_defEqPerm_2536_);
v___x_2542_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2542_);
v___x_2544_ = v___x_2529_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_mctx_2524_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_zetaDeltaFVarIds_2525_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_postponed_2526_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_diag_2527_);
v___x_2544_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_st_ref_put(v_a_2463_, v___x_2544_);
if (v_isShared_2521_ == 0)
{
v___x_2547_ = v___x_2520_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2517_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2517_);
lean_dec(v_a_2511_);
return v___x_2516_;
}
}
else
{
lean_dec(v_a_2511_);
return v___x_2516_;
}
}
v_resetjp_2557_:
{
lean_object* v_inferType_2560_; lean_object* v___x_2561_; 
v_inferType_2560_ = lean_ctor_get(v_cache_2556_, 0);
lean_inc_ref(v_inferType_2560_);
lean_dec_ref(v_cache_2556_);
lean_inc(v_a_2511_);
v___x_2561_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2508_, v___x_2509_, v_inferType_2560_, v_a_2511_);
lean_dec_ref(v_inferType_2560_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; lean_object* v_toApplicative_2563_; lean_object* v_toFunctor_2564_; lean_object* v_toSeq_2565_; lean_object* v_toSeqLeft_2566_; lean_object* v_toSeqRight_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___x_2577_; 
lean_del_object(v___x_2513_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2563_ = lean_ctor_get(v___x_2562_, 0);
v_toFunctor_2564_ = lean_ctor_get(v_toApplicative_2563_, 0);
v_toSeq_2565_ = lean_ctor_get(v_toApplicative_2563_, 2);
v_toSeqLeft_2566_ = lean_ctor_get(v_toApplicative_2563_, 3);
v_toSeqRight_2567_ = lean_ctor_get(v_toApplicative_2563_, 4);
v___f_2568_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2569_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2564_, 2);
v___f_2570_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2570_, 0, v_toFunctor_2564_);
v___f_2571_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2571_, 0, v_toFunctor_2564_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___f_2570_);
lean_ctor_set(v___x_2572_, 1, v___f_2571_);
lean_inc(v_toSeqRight_2567_);
v___f_2573_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2573_, 0, v_toSeqRight_2567_);
lean_inc(v_toSeqLeft_2566_);
v___f_2574_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2574_, 0, v_toSeqLeft_2566_);
lean_inc(v_toSeq_2565_);
v___f_2575_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2575_, 0, v_toSeq_2565_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 4, v___f_2573_);
lean_ctor_set(v___x_2558_, 3, v___f_2574_);
lean_ctor_set(v___x_2558_, 2, v___f_2575_);
lean_ctor_set(v___x_2558_, 1, v___f_2568_);
lean_ctor_set(v___x_2558_, 0, v___x_2572_);
v___x_2577_ = v___x_2558_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___f_2568_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v___f_2575_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v___f_2574_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v___f_2573_);
v___x_2577_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_toCold_2584_; lean_object* v_cancelTk_x3f_2585_; 
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
lean_ctor_set(v___x_2578_, 1, v___f_2569_);
v___x_2579_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2580_ = l_Lean_Core_instMonadRefCoreM;
v___x_2581_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2582_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2581_, v___x_2578_);
v___x_2583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2579_);
lean_ctor_set(v___x_2583_, 1, v___x_2580_);
lean_ctor_set(v___x_2583_, 2, v___x_2582_);
v_toCold_2584_ = lean_ctor_get(v_a_2464_, 0);
v_cancelTk_x3f_2585_ = lean_ctor_get(v_toCold_2584_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2585_) == 1)
{
lean_object* v_val_2586_; uint8_t v___x_2587_; 
v_val_2586_ = lean_ctor_get(v_cancelTk_x3f_2585_, 0);
v___x_2587_ = l_IO_CancelToken_isSet(v_val_2586_);
if (v___x_2587_ == 0)
{
lean_dec_ref_known(v___x_2583_, 3);
goto v___jp_2515_;
}
else
{
lean_object* v___x_2058__overap_2588_; lean_object* v___x_2589_; 
v___x_2058__overap_2588_ = l_Lean_throwInterruptException___redArg(v___x_2583_);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
v___x_2589_ = lean_apply_3(v___x_2058__overap_2588_, v_a_2464_, v_a_2465_, lean_box(0));
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_dec_ref_known(v___x_2589_, 1);
goto v___jp_2515_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_a_2511_);
lean_dec_ref(v_inferType_2461_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2583_, 3);
goto v___jp_2515_;
}
}
}
else
{
lean_object* v_val_2599_; lean_object* v___x_2601_; 
lean_del_object(v___x_2558_);
lean_dec(v_a_2511_);
lean_dec_ref(v_inferType_2461_);
v_val_2599_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v___x_2561_, 1);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v_val_2599_);
v___x_2601_ = v___x_2513_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_val_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v_inferType_2461_);
v_a_2609_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2510_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2510_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_dec_ref(v_e_2460_);
goto v___jp_2467_;
}
}
v___jp_2467_:
{
lean_object* v___x_2468_; lean_object* v_toApplicative_2469_; lean_object* v_toFunctor_2470_; lean_object* v_toSeq_2471_; lean_object* v_toSeqLeft_2472_; lean_object* v_toSeqRight_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; lean_object* v___f_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v___f_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_toCold_2489_; lean_object* v_cancelTk_x3f_2490_; 
v___x_2468_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2469_ = lean_ctor_get(v___x_2468_, 0);
v_toFunctor_2470_ = lean_ctor_get(v_toApplicative_2469_, 0);
v_toSeq_2471_ = lean_ctor_get(v_toApplicative_2469_, 2);
v_toSeqLeft_2472_ = lean_ctor_get(v_toApplicative_2469_, 3);
v_toSeqRight_2473_ = lean_ctor_get(v_toApplicative_2469_, 4);
v___f_2474_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2475_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2470_, 2);
v___f_2476_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2476_, 0, v_toFunctor_2470_);
v___f_2477_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2477_, 0, v_toFunctor_2470_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___f_2476_);
lean_ctor_set(v___x_2478_, 1, v___f_2477_);
lean_inc(v_toSeqRight_2473_);
v___f_2479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2479_, 0, v_toSeqRight_2473_);
lean_inc(v_toSeqLeft_2472_);
v___f_2480_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2480_, 0, v_toSeqLeft_2472_);
lean_inc(v_toSeq_2471_);
v___f_2481_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2481_, 0, v_toSeq_2471_);
v___x_2482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2478_);
lean_ctor_set(v___x_2482_, 1, v___f_2474_);
lean_ctor_set(v___x_2482_, 2, v___f_2481_);
lean_ctor_set(v___x_2482_, 3, v___f_2480_);
lean_ctor_set(v___x_2482_, 4, v___f_2479_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___f_2475_);
v___x_2484_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2485_ = l_Lean_Core_instMonadRefCoreM;
v___x_2486_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2487_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2486_, v___x_2483_);
v___x_2488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2484_);
lean_ctor_set(v___x_2488_, 1, v___x_2485_);
lean_ctor_set(v___x_2488_, 2, v___x_2487_);
v_toCold_2489_ = lean_ctor_get(v_a_2464_, 0);
v_cancelTk_x3f_2490_ = lean_ctor_get(v_toCold_2489_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2490_) == 1)
{
lean_object* v_val_2491_; uint8_t v___x_2492_; 
v_val_2491_ = lean_ctor_get(v_cancelTk_x3f_2490_, 0);
v___x_2492_ = l_IO_CancelToken_isSet(v_val_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_dec_ref_known(v___x_2488_, 3);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2493_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
return v___x_2493_;
}
else
{
lean_object* v___x_2031__overap_2494_; lean_object* v___x_2495_; 
v___x_2031__overap_2494_ = l_Lean_throwInterruptException___redArg(v___x_2488_);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
v___x_2495_ = lean_apply_3(v___x_2031__overap_2494_, v_a_2464_, v_a_2465_, lean_box(0));
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v___x_2496_; 
lean_dec_ref_known(v___x_2495_, 1);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2496_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
return v___x_2496_;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec_ref(v_inferType_2461_);
v_a_2497_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2495_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2495_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
else
{
lean_object* v___x_2505_; 
lean_dec_ref_known(v___x_2488_, 3);
lean_inc(v_a_2465_);
lean_inc_ref(v_a_2464_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2505_ = lean_apply_5(v_inferType_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, lean_box(0));
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2617_, lean_object* v_inferType_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2617_, v_inferType_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2677_; uint8_t v_beta_2678_; 
v___x_2677_ = l_Lean_Meta_Context_config(v___y_2626_);
v_beta_2678_ = lean_ctor_get_uint8(v___x_2677_, 13);
if (v_beta_2678_ == 0)
{
lean_dec_ref(v___x_2677_);
goto v___jp_2631_;
}
else
{
uint8_t v_iota_2679_; 
v_iota_2679_ = lean_ctor_get_uint8(v___x_2677_, 12);
if (v_iota_2679_ == 0)
{
lean_dec_ref(v___x_2677_);
goto v___jp_2631_;
}
else
{
uint8_t v_zeta_2680_; 
v_zeta_2680_ = lean_ctor_get_uint8(v___x_2677_, 15);
if (v_zeta_2680_ == 0)
{
lean_dec_ref(v___x_2677_);
goto v___jp_2631_;
}
else
{
uint8_t v_zetaHave_2681_; 
v_zetaHave_2681_ = lean_ctor_get_uint8(v___x_2677_, 18);
if (v_zetaHave_2681_ == 0)
{
lean_dec_ref(v___x_2677_);
goto v___jp_2631_;
}
else
{
uint8_t v_zetaDelta_2682_; 
v_zetaDelta_2682_ = lean_ctor_get_uint8(v___x_2677_, 16);
if (v_zetaDelta_2682_ == 0)
{
lean_dec_ref(v___x_2677_);
goto v___jp_2631_;
}
else
{
uint8_t v_etaStruct_2683_; uint8_t v_proj_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v_etaStruct_2683_ = lean_ctor_get_uint8(v___x_2677_, 10);
v_proj_2684_ = lean_ctor_get_uint8(v___x_2677_, 14);
lean_dec_ref(v___x_2677_);
v___x_2685_ = lean_box(v_proj_2684_);
v___x_2686_ = lean_obj_tag_nat(v___x_2685_);
lean_dec(v___x_2685_);
v___x_2687_ = lean_unsigned_to_nat(2u);
v___x_2688_ = lean_nat_dec_eq(v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
goto v___jp_2631_;
}
else
{
uint8_t v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = 0;
v___x_2690_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2683_, v___x_2689_);
if (v___x_2690_ == 0)
{
goto v___jp_2631_;
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_apply_5(v_x_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, lean_box(0));
return v___x_2691_;
}
}
}
}
}
}
}
v___jp_2631_:
{
lean_object* v___x_2632_; uint8_t v_foApprox_2633_; uint8_t v_ctxApprox_2634_; uint8_t v_quasiPatternApprox_2635_; uint8_t v_constApprox_2636_; uint8_t v_isDefEqStuckEx_2637_; uint8_t v_unificationHints_2638_; uint8_t v_proofIrrelevance_2639_; uint8_t v_assignSyntheticOpaque_2640_; uint8_t v_offsetCnstrs_2641_; uint8_t v_transparency_2642_; uint8_t v_univApprox_2643_; uint8_t v_zetaUnused_2644_; uint8_t v_canUnfoldPredicateConfig_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2676_; 
v___x_2632_ = l_Lean_Meta_Context_config(v___y_2626_);
v_foApprox_2633_ = lean_ctor_get_uint8(v___x_2632_, 0);
v_ctxApprox_2634_ = lean_ctor_get_uint8(v___x_2632_, 1);
v_quasiPatternApprox_2635_ = lean_ctor_get_uint8(v___x_2632_, 2);
v_constApprox_2636_ = lean_ctor_get_uint8(v___x_2632_, 3);
v_isDefEqStuckEx_2637_ = lean_ctor_get_uint8(v___x_2632_, 4);
v_unificationHints_2638_ = lean_ctor_get_uint8(v___x_2632_, 5);
v_proofIrrelevance_2639_ = lean_ctor_get_uint8(v___x_2632_, 6);
v_assignSyntheticOpaque_2640_ = lean_ctor_get_uint8(v___x_2632_, 7);
v_offsetCnstrs_2641_ = lean_ctor_get_uint8(v___x_2632_, 8);
v_transparency_2642_ = lean_ctor_get_uint8(v___x_2632_, 9);
v_univApprox_2643_ = lean_ctor_get_uint8(v___x_2632_, 11);
v_zetaUnused_2644_ = lean_ctor_get_uint8(v___x_2632_, 17);
v_canUnfoldPredicateConfig_2645_ = lean_ctor_get_uint8(v___x_2632_, 19);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2647_ = v___x_2632_;
v_isShared_2648_ = v_isSharedCheck_2676_;
goto v_resetjp_2646_;
}
else
{
lean_dec(v___x_2632_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2676_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
uint8_t v___x_2649_; uint8_t v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2653_; 
v___x_2649_ = 1;
v___x_2650_ = 0;
v___x_2651_ = 2;
if (v_isShared_2648_ == 0)
{
v___x_2653_ = v___x_2647_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 0, v_foApprox_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 1, v_ctxApprox_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 2, v_quasiPatternApprox_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 3, v_constApprox_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 4, v_isDefEqStuckEx_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 5, v_unificationHints_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 6, v_proofIrrelevance_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 7, v_assignSyntheticOpaque_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 8, v_offsetCnstrs_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 9, v_transparency_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 11, v_univApprox_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 17, v_zetaUnused_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 19, v_canUnfoldPredicateConfig_2645_);
v___x_2653_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
uint8_t v_trackZetaDelta_2654_; lean_object* v_zetaDeltaSet_2655_; lean_object* v_lctx_2656_; lean_object* v_localInstances_2657_; lean_object* v_defEqCtx_x3f_2658_; lean_object* v_synthPendingDepth_2659_; lean_object* v_customCanUnfoldPredicate_x3f_2660_; uint8_t v_univApprox_2661_; uint8_t v_inTypeClassResolution_2662_; uint8_t v_cacheInferType_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2673_; 
lean_ctor_set_uint8(v___x_2653_, 10, v___x_2650_);
lean_ctor_set_uint8(v___x_2653_, 12, v___x_2649_);
lean_ctor_set_uint8(v___x_2653_, 13, v___x_2649_);
lean_ctor_set_uint8(v___x_2653_, 14, v___x_2651_);
lean_ctor_set_uint8(v___x_2653_, 15, v___x_2649_);
lean_ctor_set_uint8(v___x_2653_, 16, v___x_2649_);
lean_ctor_set_uint8(v___x_2653_, 18, v___x_2649_);
v_trackZetaDelta_2654_ = lean_ctor_get_uint8(v___y_2626_, sizeof(void*)*7);
v_zetaDeltaSet_2655_ = lean_ctor_get(v___y_2626_, 1);
v_lctx_2656_ = lean_ctor_get(v___y_2626_, 2);
v_localInstances_2657_ = lean_ctor_get(v___y_2626_, 3);
v_defEqCtx_x3f_2658_ = lean_ctor_get(v___y_2626_, 4);
v_synthPendingDepth_2659_ = lean_ctor_get(v___y_2626_, 5);
v_customCanUnfoldPredicate_x3f_2660_ = lean_ctor_get(v___y_2626_, 6);
v_univApprox_2661_ = lean_ctor_get_uint8(v___y_2626_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2662_ = lean_ctor_get_uint8(v___y_2626_, sizeof(void*)*7 + 2);
v_cacheInferType_2663_ = lean_ctor_get_uint8(v___y_2626_, sizeof(void*)*7 + 3);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___y_2626_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___y_2626_, 0);
lean_dec(v_unused_2674_);
v___x_2665_ = v___y_2626_;
v_isShared_2666_ = v_isSharedCheck_2673_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2660_);
lean_inc(v_synthPendingDepth_2659_);
lean_inc(v_defEqCtx_x3f_2658_);
lean_inc(v_localInstances_2657_);
lean_inc(v_lctx_2656_);
lean_inc(v_zetaDeltaSet_2655_);
lean_dec(v___y_2626_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2673_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
uint64_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2667_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2653_);
v___x_2668_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2668_, 0, v___x_2653_);
lean_ctor_set_uint64(v___x_2668_, sizeof(void*)*1, v___x_2667_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2668_);
v___x_2670_ = v___x_2665_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_zetaDeltaSet_2655_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_lctx_2656_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v_localInstances_2657_);
lean_ctor_set(v_reuseFailAlloc_2672_, 4, v_defEqCtx_x3f_2658_);
lean_ctor_set(v_reuseFailAlloc_2672_, 5, v_synthPendingDepth_2659_);
lean_ctor_set(v_reuseFailAlloc_2672_, 6, v_customCanUnfoldPredicate_x3f_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*7, v_trackZetaDelta_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*7 + 1, v_univApprox_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*7 + 3, v_cacheInferType_2663_);
v___x_2670_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_apply_5(v_x_2625_, v___x_2670_, v___y_2627_, v___y_2628_, v___y_2629_, lean_box(0));
return v___x_2671_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___y_2706_; lean_object* v___x_2723_; uint8_t v_transparency_2724_; uint8_t v___x_2725_; uint8_t v___x_2726_; 
v___x_2723_ = l_Lean_Meta_Context_config(v_a_2700_);
v_transparency_2724_ = lean_ctor_get_uint8(v___x_2723_, 9);
lean_dec_ref(v___x_2723_);
v___x_2725_ = 1;
v___x_2726_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2724_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
lean_inc(v_a_2703_);
lean_inc_ref(v_a_2702_);
lean_inc(v_a_2701_);
lean_inc_ref(v_a_2700_);
v___x_2727_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
v___y_2706_ = v___x_2727_;
goto v___jp_2705_;
}
else
{
lean_object* v_keyedConfig_2728_; uint8_t v_trackZetaDelta_2729_; lean_object* v_zetaDeltaSet_2730_; lean_object* v_lctx_2731_; lean_object* v_localInstances_2732_; lean_object* v_defEqCtx_x3f_2733_; lean_object* v_synthPendingDepth_2734_; lean_object* v_customCanUnfoldPredicate_x3f_2735_; uint8_t v_univApprox_2736_; uint8_t v_inTypeClassResolution_2737_; uint8_t v_cacheInferType_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v_keyedConfig_2728_ = lean_ctor_get(v_a_2700_, 0);
v_trackZetaDelta_2729_ = lean_ctor_get_uint8(v_a_2700_, sizeof(void*)*7);
v_zetaDeltaSet_2730_ = lean_ctor_get(v_a_2700_, 1);
v_lctx_2731_ = lean_ctor_get(v_a_2700_, 2);
v_localInstances_2732_ = lean_ctor_get(v_a_2700_, 3);
v_defEqCtx_x3f_2733_ = lean_ctor_get(v_a_2700_, 4);
v_synthPendingDepth_2734_ = lean_ctor_get(v_a_2700_, 5);
v_customCanUnfoldPredicate_x3f_2735_ = lean_ctor_get(v_a_2700_, 6);
v_univApprox_2736_ = lean_ctor_get_uint8(v_a_2700_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2737_ = lean_ctor_get_uint8(v_a_2700_, sizeof(void*)*7 + 2);
v_cacheInferType_2738_ = lean_ctor_get_uint8(v_a_2700_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2728_);
v___x_2739_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2725_, v_keyedConfig_2728_);
lean_inc(v_customCanUnfoldPredicate_x3f_2735_);
lean_inc(v_synthPendingDepth_2734_);
lean_inc(v_defEqCtx_x3f_2733_);
lean_inc_ref(v_localInstances_2732_);
lean_inc_ref(v_lctx_2731_);
lean_inc(v_zetaDeltaSet_2730_);
v___x_2740_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v_zetaDeltaSet_2730_);
lean_ctor_set(v___x_2740_, 2, v_lctx_2731_);
lean_ctor_set(v___x_2740_, 3, v_localInstances_2732_);
lean_ctor_set(v___x_2740_, 4, v_defEqCtx_x3f_2733_);
lean_ctor_set(v___x_2740_, 5, v_synthPendingDepth_2734_);
lean_ctor_set(v___x_2740_, 6, v_customCanUnfoldPredicate_x3f_2735_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7, v_trackZetaDelta_2729_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7 + 1, v_univApprox_2736_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2737_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*7 + 3, v_cacheInferType_2738_);
lean_inc(v_a_2703_);
lean_inc_ref(v_a_2702_);
lean_inc(v_a_2701_);
v___x_2741_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2699_, v___x_2740_, v_a_2701_, v_a_2702_, v_a_2703_);
v___y_2706_ = v___x_2741_;
goto v___jp_2705_;
}
v___jp_2705_:
{
if (lean_obj_tag(v___y_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
v_a_2707_ = lean_ctor_get(v___y_2706_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___y_2706_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___y_2706_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___y_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
v_a_2715_ = lean_ctor_get(v___y_2706_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___y_2706_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___y_2706_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___y_2706_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2749_, lean_object* v_x_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v___y_2757_; lean_object* v___x_2774_; uint8_t v_transparency_2775_; uint8_t v___x_2776_; uint8_t v___x_2777_; 
v___x_2774_ = l_Lean_Meta_Context_config(v_a_2751_);
v_transparency_2775_ = lean_ctor_get_uint8(v___x_2774_, 9);
lean_dec_ref(v___x_2774_);
v___x_2776_ = 1;
v___x_2777_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2775_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
lean_inc(v_a_2754_);
lean_inc_ref(v_a_2753_);
lean_inc(v_a_2752_);
lean_inc_ref(v_a_2751_);
v___x_2778_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
v___y_2757_ = v___x_2778_;
goto v___jp_2756_;
}
else
{
lean_object* v_keyedConfig_2779_; uint8_t v_trackZetaDelta_2780_; lean_object* v_zetaDeltaSet_2781_; lean_object* v_lctx_2782_; lean_object* v_localInstances_2783_; lean_object* v_defEqCtx_x3f_2784_; lean_object* v_synthPendingDepth_2785_; lean_object* v_customCanUnfoldPredicate_x3f_2786_; uint8_t v_univApprox_2787_; uint8_t v_inTypeClassResolution_2788_; uint8_t v_cacheInferType_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_keyedConfig_2779_ = lean_ctor_get(v_a_2751_, 0);
v_trackZetaDelta_2780_ = lean_ctor_get_uint8(v_a_2751_, sizeof(void*)*7);
v_zetaDeltaSet_2781_ = lean_ctor_get(v_a_2751_, 1);
v_lctx_2782_ = lean_ctor_get(v_a_2751_, 2);
v_localInstances_2783_ = lean_ctor_get(v_a_2751_, 3);
v_defEqCtx_x3f_2784_ = lean_ctor_get(v_a_2751_, 4);
v_synthPendingDepth_2785_ = lean_ctor_get(v_a_2751_, 5);
v_customCanUnfoldPredicate_x3f_2786_ = lean_ctor_get(v_a_2751_, 6);
v_univApprox_2787_ = lean_ctor_get_uint8(v_a_2751_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2788_ = lean_ctor_get_uint8(v_a_2751_, sizeof(void*)*7 + 2);
v_cacheInferType_2789_ = lean_ctor_get_uint8(v_a_2751_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2779_);
v___x_2790_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2776_, v_keyedConfig_2779_);
lean_inc(v_customCanUnfoldPredicate_x3f_2786_);
lean_inc(v_synthPendingDepth_2785_);
lean_inc(v_defEqCtx_x3f_2784_);
lean_inc_ref(v_localInstances_2783_);
lean_inc_ref(v_lctx_2782_);
lean_inc(v_zetaDeltaSet_2781_);
v___x_2791_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v_zetaDeltaSet_2781_);
lean_ctor_set(v___x_2791_, 2, v_lctx_2782_);
lean_ctor_set(v___x_2791_, 3, v_localInstances_2783_);
lean_ctor_set(v___x_2791_, 4, v_defEqCtx_x3f_2784_);
lean_ctor_set(v___x_2791_, 5, v_synthPendingDepth_2785_);
lean_ctor_set(v___x_2791_, 6, v_customCanUnfoldPredicate_x3f_2786_);
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*7, v_trackZetaDelta_2780_);
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*7 + 1, v_univApprox_2787_);
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2788_);
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*7 + 3, v_cacheInferType_2789_);
lean_inc(v_a_2754_);
lean_inc_ref(v_a_2753_);
lean_inc(v_a_2752_);
v___x_2792_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2750_, v___x_2791_, v_a_2752_, v_a_2753_, v_a_2754_);
v___y_2757_ = v___x_2792_;
goto v___jp_2756_;
}
v___jp_2756_:
{
if (lean_obj_tag(v___y_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
v_a_2758_ = lean_ctor_get(v___y_2757_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___y_2757_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___y_2757_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___y_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
v_a_2766_ = lean_ctor_get(v___y_2757_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___y_2757_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___y_2757_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___y_2757_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2793_, lean_object* v_x_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2793_, v_x_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
return v_res_2800_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = l_Lean_interruptExceptionId;
v___x_2803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___x_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_){
_start:
{
lean_object* v_ks_2823_; lean_object* v_vs_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2853_; 
v_ks_2823_ = lean_ctor_get(v_x_2819_, 0);
v_vs_2824_ = lean_ctor_get(v_x_2819_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_x_2819_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2826_ = v_x_2819_;
v_isShared_2827_ = v_isSharedCheck_2853_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_vs_2824_);
lean_inc(v_ks_2823_);
lean_dec(v_x_2819_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2853_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
uint8_t v___y_2829_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = lean_array_get_size(v_ks_2823_);
v___x_2842_ = lean_nat_dec_lt(v_x_2820_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_del_object(v___x_2826_);
lean_dec(v_x_2820_);
v___x_2843_ = lean_array_push(v_ks_2823_, v_x_2821_);
v___x_2844_ = lean_array_push(v_vs_2824_, v_x_2822_);
v___x_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
return v___x_2845_;
}
else
{
lean_object* v_expr_2846_; uint64_t v_configKey_2847_; lean_object* v_k_x27_2848_; lean_object* v_expr_2849_; uint64_t v_configKey_2850_; uint8_t v___x_2851_; 
v_expr_2846_ = lean_ctor_get(v_x_2821_, 0);
v_configKey_2847_ = lean_ctor_get_uint64(v_x_2821_, sizeof(void*)*1);
v_k_x27_2848_ = lean_array_fget_borrowed(v_ks_2823_, v_x_2820_);
v_expr_2849_ = lean_ctor_get(v_k_x27_2848_, 0);
v_configKey_2850_ = lean_ctor_get_uint64(v_k_x27_2848_, sizeof(void*)*1);
v___x_2851_ = lean_expr_equal(v_expr_2846_, v_expr_2849_);
if (v___x_2851_ == 0)
{
v___y_2829_ = v___x_2851_;
goto v___jp_2828_;
}
else
{
uint8_t v___x_2852_; 
v___x_2852_ = lean_uint64_dec_eq(v_configKey_2847_, v_configKey_2850_);
v___y_2829_ = v___x_2852_;
goto v___jp_2828_;
}
}
v___jp_2828_:
{
if (v___y_2829_ == 0)
{
lean_object* v___x_2831_; 
if (v_isShared_2827_ == 0)
{
v___x_2831_ = v___x_2826_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_ks_2823_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_vs_2824_);
v___x_2831_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = lean_nat_add(v_x_2820_, v___x_2832_);
lean_dec(v_x_2820_);
v_x_2819_ = v___x_2831_;
v_x_2820_ = v___x_2833_;
goto _start;
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2836_ = lean_array_fset(v_ks_2823_, v_x_2820_, v_x_2821_);
v___x_2837_ = lean_array_fset(v_vs_2824_, v_x_2820_, v_x_2822_);
lean_dec(v_x_2820_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 1, v___x_2837_);
lean_ctor_set(v___x_2826_, 0, v___x_2836_);
v___x_2839_ = v___x_2826_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2854_, lean_object* v_k_2855_, lean_object* v_v_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2854_, v___x_2857_, v_k_2855_, v_v_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2859_, size_t v_x_2860_, size_t v_x_2861_, lean_object* v_x_2862_, lean_object* v_x_2863_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 0)
{
lean_object* v_es_2864_; size_t v___x_2865_; size_t v___x_2866_; lean_object* v_j_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_es_2864_ = lean_ctor_get(v_x_2859_, 0);
v___x_2865_ = ((size_t)31ULL);
v___x_2866_ = lean_usize_land(v_x_2860_, v___x_2865_);
v_j_2867_ = lean_usize_to_nat(v___x_2866_);
v___x_2868_ = lean_array_get_size(v_es_2864_);
v___x_2869_ = lean_nat_dec_lt(v_j_2867_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_dec(v_j_2867_);
lean_dec(v_x_2863_);
lean_dec_ref(v_x_2862_);
return v_x_2859_;
}
else
{
lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2915_; 
lean_inc_ref(v_es_2864_);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_x_2859_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; 
v_unused_2916_ = lean_ctor_get(v_x_2859_, 0);
lean_dec(v_unused_2916_);
v___x_2871_ = v_x_2859_;
v_isShared_2872_ = v_isSharedCheck_2915_;
goto v_resetjp_2870_;
}
else
{
lean_dec(v_x_2859_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2915_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v_v_2873_; lean_object* v___x_2874_; lean_object* v_xs_x27_2875_; lean_object* v___y_2877_; 
v_v_2873_ = lean_array_fget(v_es_2864_, v_j_2867_);
v___x_2874_ = lean_box(0);
v_xs_x27_2875_ = lean_array_fset(v_es_2864_, v_j_2867_, v___x_2874_);
switch(lean_obj_tag(v_v_2873_))
{
case 0:
{
lean_object* v_key_2882_; lean_object* v_val_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2900_; 
v_key_2882_ = lean_ctor_get(v_v_2873_, 0);
v_val_2883_ = lean_ctor_get(v_v_2873_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v_v_2873_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2885_ = v_v_2873_;
v_isShared_2886_ = v_isSharedCheck_2900_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_val_2883_);
lean_inc(v_key_2882_);
lean_dec(v_v_2873_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2900_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
uint8_t v___y_2888_; lean_object* v_expr_2894_; uint64_t v_configKey_2895_; lean_object* v_expr_2896_; uint64_t v_configKey_2897_; uint8_t v___x_2898_; 
v_expr_2894_ = lean_ctor_get(v_x_2862_, 0);
v_configKey_2895_ = lean_ctor_get_uint64(v_x_2862_, sizeof(void*)*1);
v_expr_2896_ = lean_ctor_get(v_key_2882_, 0);
v_configKey_2897_ = lean_ctor_get_uint64(v_key_2882_, sizeof(void*)*1);
v___x_2898_ = lean_expr_equal(v_expr_2894_, v_expr_2896_);
if (v___x_2898_ == 0)
{
v___y_2888_ = v___x_2898_;
goto v___jp_2887_;
}
else
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_uint64_dec_eq(v_configKey_2895_, v_configKey_2897_);
v___y_2888_ = v___x_2899_;
goto v___jp_2887_;
}
v___jp_2887_:
{
if (v___y_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_del_object(v___x_2885_);
v___x_2889_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2882_, v_val_2883_, v_x_2862_, v_x_2863_);
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
v___y_2877_ = v___x_2890_;
goto v___jp_2876_;
}
else
{
lean_object* v___x_2892_; 
lean_dec(v_val_2883_);
lean_dec(v_key_2882_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 1, v_x_2863_);
lean_ctor_set(v___x_2885_, 0, v_x_2862_);
v___x_2892_ = v___x_2885_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_x_2862_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_x_2863_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
v___y_2877_ = v___x_2892_;
goto v___jp_2876_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2913_; 
v_node_2901_ = lean_ctor_get(v_v_2873_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_v_2873_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2903_ = v_v_2873_;
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_node_2901_);
lean_dec(v_v_2873_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2913_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
size_t v___x_2905_; size_t v___x_2906_; size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2905_ = ((size_t)5ULL);
v___x_2906_ = lean_usize_shift_right(v_x_2860_, v___x_2905_);
v___x_2907_ = ((size_t)1ULL);
v___x_2908_ = lean_usize_add(v_x_2861_, v___x_2907_);
v___x_2909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2901_, v___x_2906_, v___x_2908_, v_x_2862_, v_x_2863_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2909_);
v___x_2911_ = v___x_2903_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v___y_2877_ = v___x_2911_;
goto v___jp_2876_;
}
}
}
default: 
{
lean_object* v___x_2914_; 
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v_x_2862_);
lean_ctor_set(v___x_2914_, 1, v_x_2863_);
v___y_2877_ = v___x_2914_;
goto v___jp_2876_;
}
}
v___jp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2878_ = lean_array_fset(v_xs_x27_2875_, v_j_2867_, v___y_2877_);
lean_dec(v_j_2867_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2878_);
v___x_2880_ = v___x_2871_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
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
else
{
lean_object* v_ks_2917_; lean_object* v_vs_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2936_; 
v_ks_2917_ = lean_ctor_get(v_x_2859_, 0);
v_vs_2918_ = lean_ctor_get(v_x_2859_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_x_2859_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2920_ = v_x_2859_;
v_isShared_2921_ = v_isSharedCheck_2936_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_vs_2918_);
lean_inc(v_ks_2917_);
lean_dec(v_x_2859_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2936_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_ks_2917_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_vs_2918_);
v___x_2923_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v_newNode_2924_; size_t v___x_2925_; uint8_t v___x_2926_; 
v_newNode_2924_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2923_, v_x_2862_, v_x_2863_);
v___x_2925_ = ((size_t)7ULL);
v___x_2926_ = lean_usize_dec_le(v___x_2925_, v_x_2861_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2927_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2924_);
v___x_2928_ = lean_unsigned_to_nat(4u);
v___x_2929_ = lean_nat_dec_lt(v___x_2927_, v___x_2928_);
lean_dec(v___x_2927_);
if (v___x_2929_ == 0)
{
lean_object* v_ks_2930_; lean_object* v_vs_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_ks_2930_ = lean_ctor_get(v_newNode_2924_, 0);
lean_inc_ref(v_ks_2930_);
v_vs_2931_ = lean_ctor_get(v_newNode_2924_, 1);
lean_inc_ref(v_vs_2931_);
lean_dec_ref(v_newNode_2924_);
v___x_2932_ = lean_unsigned_to_nat(0u);
v___x_2933_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2934_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2861_, v_ks_2930_, v_vs_2931_, v___x_2932_, v___x_2933_);
lean_dec_ref(v_vs_2931_);
lean_dec_ref(v_ks_2930_);
return v___x_2934_;
}
else
{
return v_newNode_2924_;
}
}
else
{
return v_newNode_2924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2937_, lean_object* v_keys_2938_, lean_object* v_vals_2939_, lean_object* v_i_2940_, lean_object* v_entries_2941_){
_start:
{
lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2942_ = lean_array_get_size(v_keys_2938_);
v___x_2943_ = lean_nat_dec_lt(v_i_2940_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_dec(v_i_2940_);
return v_entries_2941_;
}
else
{
lean_object* v_k_2944_; lean_object* v_expr_2945_; uint64_t v_configKey_2946_; lean_object* v_v_2947_; uint64_t v___x_2948_; uint64_t v___x_2949_; size_t v_h_2950_; size_t v___x_2951_; lean_object* v___x_2952_; size_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v_h_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_k_2944_ = lean_array_fget_borrowed(v_keys_2938_, v_i_2940_);
v_expr_2945_ = lean_ctor_get(v_k_2944_, 0);
v_configKey_2946_ = lean_ctor_get_uint64(v_k_2944_, sizeof(void*)*1);
v_v_2947_ = lean_array_fget_borrowed(v_vals_2939_, v_i_2940_);
v___x_2948_ = l_Lean_Expr_hash(v_expr_2945_);
v___x_2949_ = lean_uint64_mix_hash(v___x_2948_, v_configKey_2946_);
v_h_2950_ = lean_uint64_to_usize(v___x_2949_);
v___x_2951_ = ((size_t)5ULL);
v___x_2952_ = lean_unsigned_to_nat(1u);
v___x_2953_ = ((size_t)1ULL);
v___x_2954_ = lean_usize_sub(v_depth_2937_, v___x_2953_);
v___x_2955_ = lean_usize_mul(v___x_2951_, v___x_2954_);
v_h_2956_ = lean_usize_shift_right(v_h_2950_, v___x_2955_);
v___x_2957_ = lean_nat_add(v_i_2940_, v___x_2952_);
lean_dec(v_i_2940_);
lean_inc(v_v_2947_);
lean_inc(v_k_2944_);
v___x_2958_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2941_, v_h_2956_, v_depth_2937_, v_k_2944_, v_v_2947_);
v_i_2940_ = v___x_2957_;
v_entries_2941_ = v___x_2958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2960_, lean_object* v_keys_2961_, lean_object* v_vals_2962_, lean_object* v_i_2963_, lean_object* v_entries_2964_){
_start:
{
size_t v_depth_boxed_2965_; lean_object* v_res_2966_; 
v_depth_boxed_2965_ = lean_unbox_usize(v_depth_2960_);
lean_dec(v_depth_2960_);
v_res_2966_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2965_, v_keys_2961_, v_vals_2962_, v_i_2963_, v_entries_2964_);
lean_dec_ref(v_vals_2962_);
lean_dec_ref(v_keys_2961_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
size_t v_x_2395__boxed_2972_; size_t v_x_2396__boxed_2973_; lean_object* v_res_2974_; 
v_x_2395__boxed_2972_ = lean_unbox_usize(v_x_2968_);
lean_dec(v_x_2968_);
v_x_2396__boxed_2973_ = lean_unbox_usize(v_x_2969_);
lean_dec(v_x_2969_);
v_res_2974_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2967_, v_x_2395__boxed_2972_, v_x_2396__boxed_2973_, v_x_2970_, v_x_2971_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2975_, lean_object* v_x_2976_, lean_object* v_x_2977_){
_start:
{
lean_object* v_expr_2978_; uint64_t v_configKey_2979_; uint64_t v___x_2980_; uint64_t v___x_2981_; size_t v___x_2982_; size_t v___x_2983_; lean_object* v___x_2984_; 
v_expr_2978_ = lean_ctor_get(v_x_2976_, 0);
v_configKey_2979_ = lean_ctor_get_uint64(v_x_2976_, sizeof(void*)*1);
v___x_2980_ = l_Lean_Expr_hash(v_expr_2978_);
v___x_2981_ = lean_uint64_mix_hash(v___x_2980_, v_configKey_2979_);
v___x_2982_ = lean_uint64_to_usize(v___x_2981_);
v___x_2983_ = ((size_t)1ULL);
v___x_2984_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2975_, v___x_2982_, v___x_2983_, v_x_2976_, v_x_2977_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2985_, lean_object* v_vals_2986_, lean_object* v_i_2987_, lean_object* v_k_2988_){
_start:
{
uint8_t v___y_2990_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = lean_array_get_size(v_keys_2985_);
v___x_2997_ = lean_nat_dec_lt(v_i_2987_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v_i_2987_);
v___x_2998_ = lean_box(0);
return v___x_2998_;
}
else
{
lean_object* v_expr_2999_; uint64_t v_configKey_3000_; lean_object* v_k_x27_3001_; lean_object* v_expr_3002_; uint64_t v_configKey_3003_; uint8_t v___x_3004_; 
v_expr_2999_ = lean_ctor_get(v_k_2988_, 0);
v_configKey_3000_ = lean_ctor_get_uint64(v_k_2988_, sizeof(void*)*1);
v_k_x27_3001_ = lean_array_fget_borrowed(v_keys_2985_, v_i_2987_);
v_expr_3002_ = lean_ctor_get(v_k_x27_3001_, 0);
v_configKey_3003_ = lean_ctor_get_uint64(v_k_x27_3001_, sizeof(void*)*1);
v___x_3004_ = lean_expr_equal(v_expr_2999_, v_expr_3002_);
if (v___x_3004_ == 0)
{
v___y_2990_ = v___x_3004_;
goto v___jp_2989_;
}
else
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_uint64_dec_eq(v_configKey_3000_, v_configKey_3003_);
v___y_2990_ = v___x_3005_;
goto v___jp_2989_;
}
}
v___jp_2989_:
{
if (v___y_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_i_2987_, v___x_2991_);
lean_dec(v_i_2987_);
v_i_2987_ = v___x_2992_;
goto _start;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_array_fget_borrowed(v_vals_2986_, v_i_2987_);
lean_dec(v_i_2987_);
lean_inc(v___x_2994_);
v___x_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3006_, lean_object* v_vals_3007_, lean_object* v_i_3008_, lean_object* v_k_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3006_, v_vals_3007_, v_i_3008_, v_k_3009_);
lean_dec_ref(v_k_3009_);
lean_dec_ref(v_vals_3007_);
lean_dec_ref(v_keys_3006_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3011_, size_t v_x_3012_, lean_object* v_x_3013_){
_start:
{
if (lean_obj_tag(v_x_3011_) == 0)
{
lean_object* v_es_3014_; lean_object* v___x_3015_; size_t v___x_3016_; size_t v___x_3017_; lean_object* v_j_3018_; lean_object* v___x_3019_; 
v_es_3014_ = lean_ctor_get(v_x_3011_, 0);
v___x_3015_ = lean_box(2);
v___x_3016_ = ((size_t)31ULL);
v___x_3017_ = lean_usize_land(v_x_3012_, v___x_3016_);
v_j_3018_ = lean_usize_to_nat(v___x_3017_);
v___x_3019_ = lean_array_get_borrowed(v___x_3015_, v_es_3014_, v_j_3018_);
lean_dec(v_j_3018_);
switch(lean_obj_tag(v___x_3019_))
{
case 0:
{
lean_object* v_key_3020_; lean_object* v_val_3021_; uint8_t v___y_3023_; lean_object* v_expr_3026_; uint64_t v_configKey_3027_; lean_object* v_expr_3028_; uint64_t v_configKey_3029_; uint8_t v___x_3030_; 
v_key_3020_ = lean_ctor_get(v___x_3019_, 0);
v_val_3021_ = lean_ctor_get(v___x_3019_, 1);
v_expr_3026_ = lean_ctor_get(v_x_3013_, 0);
v_configKey_3027_ = lean_ctor_get_uint64(v_x_3013_, sizeof(void*)*1);
v_expr_3028_ = lean_ctor_get(v_key_3020_, 0);
v_configKey_3029_ = lean_ctor_get_uint64(v_key_3020_, sizeof(void*)*1);
v___x_3030_ = lean_expr_equal(v_expr_3026_, v_expr_3028_);
if (v___x_3030_ == 0)
{
v___y_3023_ = v___x_3030_;
goto v___jp_3022_;
}
else
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_uint64_dec_eq(v_configKey_3027_, v_configKey_3029_);
v___y_3023_ = v___x_3031_;
goto v___jp_3022_;
}
v___jp_3022_:
{
if (v___y_3023_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_box(0);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; 
lean_inc(v_val_3021_);
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_val_3021_);
return v___x_3025_;
}
}
}
case 1:
{
lean_object* v_node_3032_; size_t v___x_3033_; size_t v___x_3034_; 
v_node_3032_ = lean_ctor_get(v___x_3019_, 0);
v___x_3033_ = ((size_t)5ULL);
v___x_3034_ = lean_usize_shift_right(v_x_3012_, v___x_3033_);
v_x_3011_ = v_node_3032_;
v_x_3012_ = v___x_3034_;
goto _start;
}
default: 
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_box(0);
return v___x_3036_;
}
}
}
else
{
lean_object* v_ks_3037_; lean_object* v_vs_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_ks_3037_ = lean_ctor_get(v_x_3011_, 0);
v_vs_3038_ = lean_ctor_get(v_x_3011_, 1);
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3037_, v_vs_3038_, v___x_3039_, v_x_3013_);
return v___x_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3041_, lean_object* v_x_3042_, lean_object* v_x_3043_){
_start:
{
size_t v_x_2599__boxed_3044_; lean_object* v_res_3045_; 
v_x_2599__boxed_3044_ = lean_unbox_usize(v_x_3042_);
lean_dec(v_x_3042_);
v_res_3045_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3041_, v_x_2599__boxed_3044_, v_x_3043_);
lean_dec_ref(v_x_3043_);
lean_dec_ref(v_x_3041_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v_expr_3048_; uint64_t v_configKey_3049_; uint64_t v___x_3050_; uint64_t v___x_3051_; size_t v___x_3052_; lean_object* v___x_3053_; 
v_expr_3048_ = lean_ctor_get(v_x_3047_, 0);
v_configKey_3049_ = lean_ctor_get_uint64(v_x_3047_, sizeof(void*)*1);
v___x_3050_ = l_Lean_Expr_hash(v_expr_3048_);
v___x_3051_ = lean_uint64_mix_hash(v___x_3050_, v_configKey_3049_);
v___x_3052_ = lean_uint64_to_usize(v___x_3051_);
v___x_3053_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3046_, v___x_3052_, v_x_3047_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3054_, lean_object* v_x_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3054_, v_x_3055_);
lean_dec_ref(v_x_3055_);
lean_dec_ref(v_x_3054_);
return v_res_3056_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3059_ = l_Lean_stringToMessageData(v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
switch(lean_obj_tag(v_e_3060_))
{
case 0:
{
lean_object* v_deBruijnIndex_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_deBruijnIndex_3098_ = lean_ctor_get(v_e_3060_, 0);
lean_inc(v_deBruijnIndex_3098_);
lean_dec_ref_known(v_e_3060_, 1);
v___x_3099_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3100_ = l_Lean_mkBVar(v_deBruijnIndex_3098_);
v___x_3101_ = l_Lean_MessageData_ofExpr(v___x_3100_);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3099_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3102_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3103_;
}
case 1:
{
lean_object* v_fvarId_3104_; lean_object* v___x_3105_; 
v_fvarId_3104_ = lean_ctor_get(v_e_3060_, 0);
lean_inc(v_fvarId_3104_);
lean_dec_ref_known(v_e_3060_, 1);
v___x_3105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3104_, v_a_3061_, v_a_3063_, v_a_3064_);
return v___x_3105_;
}
case 2:
{
lean_object* v_mvarId_3106_; lean_object* v___x_3107_; 
v_mvarId_3106_ = lean_ctor_get(v_e_3060_, 0);
lean_inc(v_mvarId_3106_);
lean_dec_ref_known(v_e_3060_, 1);
v___x_3107_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3106_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3107_;
}
case 3:
{
lean_object* v_u_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v_u_3108_ = lean_ctor_get(v_e_3060_, 0);
lean_inc(v_u_3108_);
lean_dec_ref_known(v_e_3060_, 1);
v___x_3109_ = l_Lean_Level_succ___override(v_u_3108_);
v___x_3110_ = l_Lean_mkSort(v___x_3109_);
v___x_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
case 4:
{
lean_object* v_declName_3112_; lean_object* v_us_3113_; 
v_declName_3112_ = lean_ctor_get(v_e_3060_, 0);
lean_inc(v_declName_3112_);
v_us_3113_ = lean_ctor_get(v_e_3060_, 1);
lean_inc(v_us_3113_);
if (lean_obj_tag(v_us_3113_) == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref_known(v_e_3060_, 2);
v___x_3130_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3112_, v_us_3113_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3130_;
}
else
{
uint8_t v_cacheInferType_3131_; 
v_cacheInferType_3131_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3131_ == 0)
{
lean_dec_ref_known(v_e_3060_, 2);
goto v___jp_3114_;
}
else
{
uint8_t v___x_3132_; 
v___x_3132_ = l_Lean_Expr_hasMVar(v_e_3060_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3199_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3199_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3199_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3178_; lean_object* v_cache_3179_; lean_object* v_inferType_3180_; lean_object* v___x_3181_; 
v___x_3178_ = lean_st_ref_get(v_a_3062_);
v_cache_3179_ = lean_ctor_get(v___x_3178_, 1);
lean_inc_ref(v_cache_3179_);
lean_dec(v___x_3178_);
v_inferType_3180_ = lean_ctor_get(v_cache_3179_, 0);
lean_inc_ref(v_inferType_3180_);
lean_dec_ref(v_cache_3179_);
v___x_3181_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3180_, v_a_3134_);
lean_dec_ref(v_inferType_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_toCold_3182_; lean_object* v_cancelTk_x3f_3183_; 
lean_del_object(v___x_3136_);
v_toCold_3182_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3183_ = lean_ctor_get(v_toCold_3182_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3183_) == 1)
{
lean_object* v_val_3184_; uint8_t v___x_3185_; 
v_val_3184_ = lean_ctor_get(v_cancelTk_x3f_3183_, 0);
v___x_3185_ = l_IO_CancelToken_isSet(v_val_3184_);
if (v___x_3185_ == 0)
{
goto v___jp_3138_;
}
else
{
lean_object* v___x_3186_; lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_a_3134_);
lean_dec(v_us_3113_);
lean_dec(v_declName_3112_);
v___x_3186_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
goto v___jp_3138_;
}
}
else
{
lean_object* v_val_3195_; lean_object* v___x_3197_; 
lean_dec(v_a_3134_);
lean_dec(v_us_3113_);
lean_dec(v_declName_3112_);
v_val_3195_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_val_3195_);
lean_dec_ref_known(v___x_3181_, 1);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v_val_3195_);
v___x_3197_ = v___x_3136_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_val_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
v___jp_3138_:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3112_, v_us_3113_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; uint8_t v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v___x_3141_ = l_Lean_Expr_hasMVar(v_a_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3176_; 
lean_inc(v_a_3140_);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v___x_3139_, 0);
lean_dec(v_unused_3177_);
v___x_3143_ = v___x_3139_;
v_isShared_3144_ = v_isSharedCheck_3176_;
goto v_resetjp_3142_;
}
else
{
lean_dec(v___x_3139_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3176_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v_cache_3146_; lean_object* v_mctx_3147_; lean_object* v_zetaDeltaFVarIds_3148_; lean_object* v_postponed_3149_; lean_object* v_diag_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3175_; 
v___x_3145_ = lean_st_ref_take(v_a_3062_);
v_cache_3146_ = lean_ctor_get(v___x_3145_, 1);
v_mctx_3147_ = lean_ctor_get(v___x_3145_, 0);
v_zetaDeltaFVarIds_3148_ = lean_ctor_get(v___x_3145_, 2);
v_postponed_3149_ = lean_ctor_get(v___x_3145_, 3);
v_diag_3150_ = lean_ctor_get(v___x_3145_, 4);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3152_ = v___x_3145_;
v_isShared_3153_ = v_isSharedCheck_3175_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_diag_3150_);
lean_inc(v_postponed_3149_);
lean_inc(v_zetaDeltaFVarIds_3148_);
lean_inc(v_cache_3146_);
lean_inc(v_mctx_3147_);
lean_dec(v___x_3145_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3175_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_inferType_3154_; lean_object* v_funInfo_3155_; lean_object* v_synthInstance_3156_; lean_object* v_whnf_3157_; lean_object* v_defEqTrans_3158_; lean_object* v_defEqPerm_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3174_; 
v_inferType_3154_ = lean_ctor_get(v_cache_3146_, 0);
v_funInfo_3155_ = lean_ctor_get(v_cache_3146_, 1);
v_synthInstance_3156_ = lean_ctor_get(v_cache_3146_, 2);
v_whnf_3157_ = lean_ctor_get(v_cache_3146_, 3);
v_defEqTrans_3158_ = lean_ctor_get(v_cache_3146_, 4);
v_defEqPerm_3159_ = lean_ctor_get(v_cache_3146_, 5);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_cache_3146_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3161_ = v_cache_3146_;
v_isShared_3162_ = v_isSharedCheck_3174_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_defEqPerm_3159_);
lean_inc(v_defEqTrans_3158_);
lean_inc(v_whnf_3157_);
lean_inc(v_synthInstance_3156_);
lean_inc(v_funInfo_3155_);
lean_inc(v_inferType_3154_);
lean_dec(v_cache_3146_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3174_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_inc(v_a_3140_);
v___x_3163_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3154_, v_a_3134_, v_a_3140_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3163_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_funInfo_3155_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_synthInstance_3156_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_whnf_3157_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_defEqTrans_3158_);
lean_ctor_set(v_reuseFailAlloc_3173_, 5, v_defEqPerm_3159_);
v___x_3165_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3167_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 1, v___x_3165_);
v___x_3167_ = v___x_3152_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_mctx_3147_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_zetaDeltaFVarIds_3148_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_postponed_3149_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_diag_3150_);
v___x_3167_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = lean_st_ref_put(v_a_3062_, v___x_3167_);
if (v_isShared_3144_ == 0)
{
v___x_3170_ = v___x_3143_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3140_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3134_);
return v___x_3139_;
}
}
else
{
lean_dec(v_a_3134_);
return v___x_3139_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_us_3113_);
lean_dec(v_declName_3112_);
v_a_3200_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3133_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3133_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3060_, 2);
goto v___jp_3114_;
}
}
}
v___jp_3114_:
{
lean_object* v_toCold_3115_; lean_object* v_cancelTk_x3f_3116_; 
v_toCold_3115_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3116_ = lean_ctor_get(v_toCold_3115_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3116_) == 1)
{
lean_object* v_val_3117_; uint8_t v___x_3118_; 
v_val_3117_ = lean_ctor_get(v_cancelTk_x3f_3116_, 0);
v___x_3118_ = l_IO_CancelToken_isSet(v_val_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
v___x_3119_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3112_, v_us_3113_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_us_3113_);
lean_dec(v_declName_3112_);
v___x_3120_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v___x_3129_; 
v___x_3129_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3112_, v_us_3113_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3129_;
}
}
}
case 5:
{
lean_object* v_fn_3208_; uint8_t v_cacheInferType_3209_; lean_object* v_nargs_3210_; lean_object* v___x_3211_; lean_object* v_dummy_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_fn_3208_ = lean_ctor_get(v_e_3060_, 0);
v_cacheInferType_3209_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*7 + 3);
v_nargs_3210_ = l_Lean_Expr_getAppNumArgs(v_e_3060_);
v___x_3211_ = l_Lean_Expr_getAppFn(v_fn_3208_);
v_dummy_3212_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3210_);
v___x_3213_ = lean_mk_array(v_nargs_3210_, v_dummy_3212_);
v___x_3214_ = lean_unsigned_to_nat(1u);
v___x_3215_ = lean_nat_sub(v_nargs_3210_, v___x_3214_);
lean_dec(v_nargs_3210_);
lean_inc_ref(v_e_3060_);
v___x_3216_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3060_, v___x_3213_, v___x_3215_);
if (v_cacheInferType_3209_ == 0)
{
lean_dec_ref_known(v_e_3060_, 2);
goto v___jp_3217_;
}
else
{
uint8_t v___x_3233_; 
v___x_3233_ = l_Lean_Expr_hasMVar(v_e_3060_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3060_, v_a_3061_);
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
v___x_3279_ = lean_st_ref_get(v_a_3062_);
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
v_toCold_3283_ = lean_ctor_get(v_a_3063_, 0);
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
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
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
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
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
v___x_3240_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3211_, v___x_3216_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec_ref(v___x_3216_);
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
v___x_3246_ = lean_st_ref_take(v_a_3062_);
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
v___x_3269_ = lean_st_ref_put(v_a_3062_, v___x_3268_);
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
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
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
lean_dec_ref_known(v_e_3060_, 2);
goto v___jp_3217_;
}
}
v___jp_3217_:
{
lean_object* v_toCold_3218_; lean_object* v_cancelTk_x3f_3219_; 
v_toCold_3218_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3219_ = lean_ctor_get(v_toCold_3218_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3219_) == 1)
{
lean_object* v_val_3220_; uint8_t v___x_3221_; 
v_val_3220_ = lean_ctor_get(v_cancelTk_x3f_3219_, 0);
v___x_3221_ = l_IO_CancelToken_isSet(v_val_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3211_, v___x_3216_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec_ref(v___x_3216_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v___x_3216_);
lean_dec_ref(v___x_3211_);
v___x_3223_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
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
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
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
else
{
lean_object* v___x_3232_; 
v___x_3232_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3211_, v___x_3216_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec_ref(v___x_3216_);
return v___x_3232_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3309_; 
v_cacheInferType_3309_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3309_ == 0)
{
goto v___jp_3082_;
}
else
{
uint8_t v___x_3310_; 
v___x_3310_ = l_Lean_Expr_hasMVar(v_e_3060_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; 
lean_inc_ref(v_e_3060_);
v___x_3311_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3377_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3377_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3377_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3356_; lean_object* v_cache_3357_; lean_object* v_inferType_3358_; lean_object* v___x_3359_; 
v___x_3356_ = lean_st_ref_get(v_a_3062_);
v_cache_3357_ = lean_ctor_get(v___x_3356_, 1);
lean_inc_ref(v_cache_3357_);
lean_dec(v___x_3356_);
v_inferType_3358_ = lean_ctor_get(v_cache_3357_, 0);
lean_inc_ref(v_inferType_3358_);
lean_dec_ref(v_cache_3357_);
v___x_3359_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3358_, v_a_3312_);
lean_dec_ref(v_inferType_3358_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_toCold_3360_; lean_object* v_cancelTk_x3f_3361_; 
lean_del_object(v___x_3314_);
v_toCold_3360_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3361_ = lean_ctor_get(v_toCold_3360_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3361_) == 1)
{
lean_object* v_val_3362_; uint8_t v___x_3363_; 
v_val_3362_ = lean_ctor_get(v_cancelTk_x3f_3361_, 0);
v___x_3363_ = l_IO_CancelToken_isSet(v_val_3362_);
if (v___x_3363_ == 0)
{
goto v___jp_3316_;
}
else
{
lean_object* v___x_3364_; lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_a_3312_);
lean_dec_ref_known(v_e_3060_, 3);
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
goto v___jp_3316_;
}
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3375_; 
lean_dec(v_a_3312_);
lean_dec_ref_known(v_e_3060_, 3);
v_val_3373_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_val_3373_);
lean_dec_ref_known(v___x_3359_, 1);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v_val_3373_);
v___x_3375_ = v___x_3314_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_val_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
v___jp_3316_:
{
lean_object* v___x_3317_; 
v___x_3317_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; uint8_t v___x_3319_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v___x_3319_ = l_Lean_Expr_hasMVar(v_a_3318_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3354_; 
lean_inc(v_a_3318_);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3354_ == 0)
{
lean_object* v_unused_3355_; 
v_unused_3355_ = lean_ctor_get(v___x_3317_, 0);
lean_dec(v_unused_3355_);
v___x_3321_ = v___x_3317_;
v_isShared_3322_ = v_isSharedCheck_3354_;
goto v_resetjp_3320_;
}
else
{
lean_dec(v___x_3317_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3354_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v_cache_3324_; lean_object* v_mctx_3325_; lean_object* v_zetaDeltaFVarIds_3326_; lean_object* v_postponed_3327_; lean_object* v_diag_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3353_; 
v___x_3323_ = lean_st_ref_take(v_a_3062_);
v_cache_3324_ = lean_ctor_get(v___x_3323_, 1);
v_mctx_3325_ = lean_ctor_get(v___x_3323_, 0);
v_zetaDeltaFVarIds_3326_ = lean_ctor_get(v___x_3323_, 2);
v_postponed_3327_ = lean_ctor_get(v___x_3323_, 3);
v_diag_3328_ = lean_ctor_get(v___x_3323_, 4);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3330_ = v___x_3323_;
v_isShared_3331_ = v_isSharedCheck_3353_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_diag_3328_);
lean_inc(v_postponed_3327_);
lean_inc(v_zetaDeltaFVarIds_3326_);
lean_inc(v_cache_3324_);
lean_inc(v_mctx_3325_);
lean_dec(v___x_3323_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3353_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_inferType_3332_; lean_object* v_funInfo_3333_; lean_object* v_synthInstance_3334_; lean_object* v_whnf_3335_; lean_object* v_defEqTrans_3336_; lean_object* v_defEqPerm_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3352_; 
v_inferType_3332_ = lean_ctor_get(v_cache_3324_, 0);
v_funInfo_3333_ = lean_ctor_get(v_cache_3324_, 1);
v_synthInstance_3334_ = lean_ctor_get(v_cache_3324_, 2);
v_whnf_3335_ = lean_ctor_get(v_cache_3324_, 3);
v_defEqTrans_3336_ = lean_ctor_get(v_cache_3324_, 4);
v_defEqPerm_3337_ = lean_ctor_get(v_cache_3324_, 5);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_cache_3324_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3339_ = v_cache_3324_;
v_isShared_3340_ = v_isSharedCheck_3352_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_defEqPerm_3337_);
lean_inc(v_defEqTrans_3336_);
lean_inc(v_whnf_3335_);
lean_inc(v_synthInstance_3334_);
lean_inc(v_funInfo_3333_);
lean_inc(v_inferType_3332_);
lean_dec(v_cache_3324_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3352_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
lean_inc(v_a_3318_);
v___x_3341_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3332_, v_a_3312_, v_a_3318_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3341_);
v___x_3343_ = v___x_3339_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_funInfo_3333_);
lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_synthInstance_3334_);
lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_whnf_3335_);
lean_ctor_set(v_reuseFailAlloc_3351_, 4, v_defEqTrans_3336_);
lean_ctor_set(v_reuseFailAlloc_3351_, 5, v_defEqPerm_3337_);
v___x_3343_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3343_);
v___x_3345_ = v___x_3330_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_mctx_3325_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_zetaDeltaFVarIds_3326_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_postponed_3327_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_diag_3328_);
v___x_3345_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_st_ref_put(v_a_3062_, v___x_3345_);
if (v_isShared_3322_ == 0)
{
v___x_3348_ = v___x_3321_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3318_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3312_);
return v___x_3317_;
}
}
else
{
lean_dec(v_a_3312_);
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec_ref_known(v_e_3060_, 3);
v_a_3378_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3311_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3311_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
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
else
{
goto v___jp_3082_;
}
}
}
case 9:
{
lean_object* v_a_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_a_3386_ = lean_ctor_get(v_e_3060_, 0);
lean_inc_ref(v_a_3386_);
lean_dec_ref_known(v_e_3060_, 1);
v___x_3387_ = l_Lean_Literal_type(v_a_3386_);
lean_dec_ref(v_a_3386_);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
case 10:
{
lean_object* v_expr_3389_; 
v_expr_3389_ = lean_ctor_get(v_e_3060_, 1);
lean_inc_ref(v_expr_3389_);
lean_dec_ref_known(v_e_3060_, 2);
v_e_3060_ = v_expr_3389_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3391_; lean_object* v_idx_3392_; lean_object* v_struct_3393_; uint8_t v_cacheInferType_3410_; 
v_typeName_3391_ = lean_ctor_get(v_e_3060_, 0);
lean_inc(v_typeName_3391_);
v_idx_3392_ = lean_ctor_get(v_e_3060_, 1);
lean_inc(v_idx_3392_);
v_struct_3393_ = lean_ctor_get(v_e_3060_, 2);
lean_inc_ref(v_struct_3393_);
v_cacheInferType_3410_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3410_ == 0)
{
lean_dec_ref_known(v_e_3060_, 3);
goto v___jp_3394_;
}
else
{
uint8_t v___x_3411_; 
v___x_3411_ = l_Lean_Expr_hasMVar(v_e_3060_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3060_, v_a_3061_);
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
v___x_3457_ = lean_st_ref_get(v_a_3062_);
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
v_toCold_3461_ = lean_ctor_get(v_a_3063_, 0);
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
lean_dec_ref(v_struct_3393_);
lean_dec(v_idx_3392_);
lean_dec(v_typeName_3391_);
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
lean_dec_ref(v_struct_3393_);
lean_dec(v_idx_3392_);
lean_dec(v_typeName_3391_);
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
v___x_3418_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3391_, v_idx_3392_, v_struct_3393_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
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
v___x_3424_ = lean_st_ref_take(v_a_3062_);
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
v___x_3447_ = lean_st_ref_put(v_a_3062_, v___x_3446_);
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
lean_dec_ref(v_struct_3393_);
lean_dec(v_idx_3392_);
lean_dec(v_typeName_3391_);
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
lean_dec_ref_known(v_e_3060_, 3);
goto v___jp_3394_;
}
}
v___jp_3394_:
{
lean_object* v_toCold_3395_; lean_object* v_cancelTk_x3f_3396_; 
v_toCold_3395_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3396_ = lean_ctor_get(v_toCold_3395_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3396_) == 1)
{
lean_object* v_val_3397_; uint8_t v___x_3398_; 
v_val_3397_ = lean_ctor_get(v_cancelTk_x3f_3396_, 0);
v___x_3398_ = l_IO_CancelToken_isSet(v_val_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3391_, v_idx_3392_, v_struct_3393_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec_ref(v_struct_3393_);
lean_dec(v_idx_3392_);
lean_dec(v_typeName_3391_);
v___x_3400_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
else
{
lean_object* v___x_3409_; 
v___x_3409_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3391_, v_idx_3392_, v_struct_3393_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3409_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3487_; 
v_cacheInferType_3487_ = lean_ctor_get_uint8(v_a_3061_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3487_ == 0)
{
goto v___jp_3066_;
}
else
{
uint8_t v___x_3488_; 
v___x_3488_ = l_Lean_Expr_hasMVar(v_e_3060_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; 
lean_inc_ref(v_e_3060_);
v___x_3489_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3060_, v_a_3061_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3555_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3555_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3555_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3534_; lean_object* v_cache_3535_; lean_object* v_inferType_3536_; lean_object* v___x_3537_; 
v___x_3534_ = lean_st_ref_get(v_a_3062_);
v_cache_3535_ = lean_ctor_get(v___x_3534_, 1);
lean_inc_ref(v_cache_3535_);
lean_dec(v___x_3534_);
v_inferType_3536_ = lean_ctor_get(v_cache_3535_, 0);
lean_inc_ref(v_inferType_3536_);
lean_dec_ref(v_cache_3535_);
v___x_3537_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3536_, v_a_3490_);
lean_dec_ref(v_inferType_3536_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_toCold_3538_; lean_object* v_cancelTk_x3f_3539_; 
lean_del_object(v___x_3492_);
v_toCold_3538_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3539_ = lean_ctor_get(v_toCold_3538_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3539_) == 1)
{
lean_object* v_val_3540_; uint8_t v___x_3541_; 
v_val_3540_ = lean_ctor_get(v_cancelTk_x3f_3539_, 0);
v___x_3541_ = l_IO_CancelToken_isSet(v_val_3540_);
if (v___x_3541_ == 0)
{
goto v___jp_3494_;
}
else
{
lean_object* v___x_3542_; lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_a_3490_);
lean_dec_ref(v_e_3060_);
v___x_3542_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3542_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3542_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
goto v___jp_3494_;
}
}
else
{
lean_object* v_val_3551_; lean_object* v___x_3553_; 
lean_dec(v_a_3490_);
lean_dec_ref(v_e_3060_);
v_val_3551_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_val_3551_);
lean_dec_ref_known(v___x_3537_, 1);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v_val_3551_);
v___x_3553_ = v___x_3492_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_val_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
v___jp_3494_:
{
lean_object* v___x_3495_; 
v___x_3495_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; uint8_t v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v___x_3497_ = l_Lean_Expr_hasMVar(v_a_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3532_; 
lean_inc(v_a_3496_);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v___x_3495_, 0);
lean_dec(v_unused_3533_);
v___x_3499_ = v___x_3495_;
v_isShared_3500_ = v_isSharedCheck_3532_;
goto v_resetjp_3498_;
}
else
{
lean_dec(v___x_3495_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3532_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v_cache_3502_; lean_object* v_mctx_3503_; lean_object* v_zetaDeltaFVarIds_3504_; lean_object* v_postponed_3505_; lean_object* v_diag_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3531_; 
v___x_3501_ = lean_st_ref_take(v_a_3062_);
v_cache_3502_ = lean_ctor_get(v___x_3501_, 1);
v_mctx_3503_ = lean_ctor_get(v___x_3501_, 0);
v_zetaDeltaFVarIds_3504_ = lean_ctor_get(v___x_3501_, 2);
v_postponed_3505_ = lean_ctor_get(v___x_3501_, 3);
v_diag_3506_ = lean_ctor_get(v___x_3501_, 4);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3508_ = v___x_3501_;
v_isShared_3509_ = v_isSharedCheck_3531_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_diag_3506_);
lean_inc(v_postponed_3505_);
lean_inc(v_zetaDeltaFVarIds_3504_);
lean_inc(v_cache_3502_);
lean_inc(v_mctx_3503_);
lean_dec(v___x_3501_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3531_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v_inferType_3510_; lean_object* v_funInfo_3511_; lean_object* v_synthInstance_3512_; lean_object* v_whnf_3513_; lean_object* v_defEqTrans_3514_; lean_object* v_defEqPerm_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3530_; 
v_inferType_3510_ = lean_ctor_get(v_cache_3502_, 0);
v_funInfo_3511_ = lean_ctor_get(v_cache_3502_, 1);
v_synthInstance_3512_ = lean_ctor_get(v_cache_3502_, 2);
v_whnf_3513_ = lean_ctor_get(v_cache_3502_, 3);
v_defEqTrans_3514_ = lean_ctor_get(v_cache_3502_, 4);
v_defEqPerm_3515_ = lean_ctor_get(v_cache_3502_, 5);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_cache_3502_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3517_ = v_cache_3502_;
v_isShared_3518_ = v_isSharedCheck_3530_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_defEqPerm_3515_);
lean_inc(v_defEqTrans_3514_);
lean_inc(v_whnf_3513_);
lean_inc(v_synthInstance_3512_);
lean_inc(v_funInfo_3511_);
lean_inc(v_inferType_3510_);
lean_dec(v_cache_3502_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3530_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v___x_3521_; 
lean_inc(v_a_3496_);
v___x_3519_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3510_, v_a_3490_, v_a_3496_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v___x_3519_);
v___x_3521_ = v___x_3517_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_funInfo_3511_);
lean_ctor_set(v_reuseFailAlloc_3529_, 2, v_synthInstance_3512_);
lean_ctor_set(v_reuseFailAlloc_3529_, 3, v_whnf_3513_);
lean_ctor_set(v_reuseFailAlloc_3529_, 4, v_defEqTrans_3514_);
lean_ctor_set(v_reuseFailAlloc_3529_, 5, v_defEqPerm_3515_);
v___x_3521_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v___x_3521_);
v___x_3523_ = v___x_3508_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_mctx_3503_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_zetaDeltaFVarIds_3504_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_postponed_3505_);
lean_ctor_set(v_reuseFailAlloc_3528_, 4, v_diag_3506_);
v___x_3523_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = lean_st_ref_put(v_a_3062_, v___x_3523_);
if (v_isShared_3500_ == 0)
{
v___x_3526_ = v___x_3499_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3496_);
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
lean_dec(v_a_3490_);
return v___x_3495_;
}
}
else
{
lean_dec(v_a_3490_);
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v_e_3060_);
v_a_3556_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3489_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3489_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
goto v___jp_3066_;
}
}
}
}
v___jp_3066_:
{
lean_object* v_toCold_3067_; lean_object* v_cancelTk_x3f_3068_; 
v_toCold_3067_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3068_ = lean_ctor_get(v_toCold_3067_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3068_) == 1)
{
lean_object* v_val_3069_; uint8_t v___x_3070_; 
v_val_3069_ = lean_ctor_get(v_cancelTk_x3f_3068_, 0);
v___x_3070_ = l_IO_CancelToken_isSet(v_val_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v_e_3060_);
v___x_3072_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v___x_3081_; 
v___x_3081_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3081_;
}
}
v___jp_3082_:
{
lean_object* v_toCold_3083_; lean_object* v_cancelTk_x3f_3084_; 
v_toCold_3083_ = lean_ctor_get(v_a_3063_, 0);
v_cancelTk_x3f_3084_ = lean_ctor_get(v_toCold_3083_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3084_) == 1)
{
lean_object* v_val_3085_; uint8_t v___x_3086_; 
v_val_3085_ = lean_ctor_get(v_cancelTk_x3f_3084_, 0);
v___x_3086_ = l_IO_CancelToken_isSet(v_val_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; 
v___x_3087_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v_e_3060_);
v___x_3088_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v___x_3097_; 
v___x_3097_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
return v___x_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3572_, v_x_3573_, v_x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3576_, lean_object* v_x_3577_, lean_object* v_x_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3577_, v_x_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3580_, v_x_3581_, v_x_3582_);
lean_dec_ref(v_x_3582_);
lean_dec_ref(v_x_3581_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3584_, lean_object* v_x_3585_, size_t v_x_3586_, size_t v_x_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3585_, v_x_3586_, v_x_3587_, v_x_3588_, v_x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
size_t v_x_3637__boxed_3597_; size_t v_x_3638__boxed_3598_; lean_object* v_res_3599_; 
v_x_3637__boxed_3597_ = lean_unbox_usize(v_x_3593_);
lean_dec(v_x_3593_);
v_x_3638__boxed_3598_ = lean_unbox_usize(v_x_3594_);
lean_dec(v_x_3594_);
v_res_3599_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3591_, v_x_3592_, v_x_3637__boxed_3597_, v_x_3638__boxed_3598_, v_x_3595_, v_x_3596_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3600_, lean_object* v_x_3601_, size_t v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3601_, v_x_3602_, v_x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
size_t v_x_3654__boxed_3609_; lean_object* v_res_3610_; 
v_x_3654__boxed_3609_ = lean_unbox_usize(v_x_3607_);
lean_dec(v_x_3607_);
v_res_3610_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3605_, v_x_3606_, v_x_3654__boxed_3609_, v_x_3608_);
lean_dec_ref(v_x_3608_);
lean_dec_ref(v_x_3606_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3611_, lean_object* v_n_3612_, lean_object* v_k_3613_, lean_object* v_v_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3612_, v_k_3613_, v_v_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3616_, size_t v_depth_3617_, lean_object* v_keys_3618_, lean_object* v_vals_3619_, lean_object* v_heq_3620_, lean_object* v_i_3621_, lean_object* v_entries_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3617_, v_keys_3618_, v_vals_3619_, v_i_3621_, v_entries_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3624_, lean_object* v_depth_3625_, lean_object* v_keys_3626_, lean_object* v_vals_3627_, lean_object* v_heq_3628_, lean_object* v_i_3629_, lean_object* v_entries_3630_){
_start:
{
size_t v_depth_boxed_3631_; lean_object* v_res_3632_; 
v_depth_boxed_3631_ = lean_unbox_usize(v_depth_3625_);
lean_dec(v_depth_3625_);
v_res_3632_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3624_, v_depth_boxed_3631_, v_keys_3626_, v_vals_3627_, v_heq_3628_, v_i_3629_, v_entries_3630_);
lean_dec_ref(v_vals_3627_);
lean_dec_ref(v_keys_3626_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3633_, lean_object* v_keys_3634_, lean_object* v_vals_3635_, lean_object* v_heq_3636_, lean_object* v_i_3637_, lean_object* v_k_3638_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3634_, v_vals_3635_, v_i_3637_, v_k_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3640_, lean_object* v_keys_3641_, lean_object* v_vals_3642_, lean_object* v_heq_3643_, lean_object* v_i_3644_, lean_object* v_k_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3640_, v_keys_3641_, v_vals_3642_, v_heq_3643_, v_i_3644_, v_k_3645_);
lean_dec_ref(v_k_3645_);
lean_dec_ref(v_vals_3642_);
lean_dec_ref(v_keys_3641_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3648_, v_x_3649_, v_x_3650_, v_x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = l_Lean_maxRecDepthErrorMessage;
v___x_3659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3661_ = l_Lean_MessageData_ofFormat(v___x_3660_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3663_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3664_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
lean_ctor_set(v___x_3664_, 1, v___x_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3665_){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3668_, 0, v_ref_3665_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3670_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3673_, lean_object* v_ref_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3674_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3681_, lean_object* v_ref_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3681_, v_ref_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v___x_3741_; uint8_t v_beta_3742_; 
v___x_3741_ = l_Lean_Meta_Context_config(v___y_3690_);
v_beta_3742_ = lean_ctor_get_uint8(v___x_3741_, 13);
if (v_beta_3742_ == 0)
{
lean_dec_ref(v___x_3741_);
goto v___jp_3695_;
}
else
{
uint8_t v_iota_3743_; 
v_iota_3743_ = lean_ctor_get_uint8(v___x_3741_, 12);
if (v_iota_3743_ == 0)
{
lean_dec_ref(v___x_3741_);
goto v___jp_3695_;
}
else
{
uint8_t v_zeta_3744_; 
v_zeta_3744_ = lean_ctor_get_uint8(v___x_3741_, 15);
if (v_zeta_3744_ == 0)
{
lean_dec_ref(v___x_3741_);
goto v___jp_3695_;
}
else
{
uint8_t v_zetaHave_3745_; 
v_zetaHave_3745_ = lean_ctor_get_uint8(v___x_3741_, 18);
if (v_zetaHave_3745_ == 0)
{
lean_dec_ref(v___x_3741_);
goto v___jp_3695_;
}
else
{
uint8_t v_zetaDelta_3746_; 
v_zetaDelta_3746_ = lean_ctor_get_uint8(v___x_3741_, 16);
if (v_zetaDelta_3746_ == 0)
{
lean_dec_ref(v___x_3741_);
goto v___jp_3695_;
}
else
{
uint8_t v_etaStruct_3747_; uint8_t v_proj_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; uint8_t v___x_3752_; 
v_etaStruct_3747_ = lean_ctor_get_uint8(v___x_3741_, 10);
v_proj_3748_ = lean_ctor_get_uint8(v___x_3741_, 14);
lean_dec_ref(v___x_3741_);
v___x_3749_ = lean_box(v_proj_3748_);
v___x_3750_ = lean_obj_tag_nat(v___x_3749_);
lean_dec(v___x_3749_);
v___x_3751_ = lean_unsigned_to_nat(2u);
v___x_3752_ = lean_nat_dec_eq(v___x_3750_, v___x_3751_);
if (v___x_3752_ == 0)
{
goto v___jp_3695_;
}
else
{
uint8_t v___x_3753_; uint8_t v___x_3754_; 
v___x_3753_ = 0;
v___x_3754_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3747_, v___x_3753_);
if (v___x_3754_ == 0)
{
goto v___jp_3695_;
}
else
{
lean_object* v___x_3755_; 
v___x_3755_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec_ref(v___y_3690_);
return v___x_3755_;
}
}
}
}
}
}
}
v___jp_3695_:
{
lean_object* v___x_3696_; uint8_t v_foApprox_3697_; uint8_t v_ctxApprox_3698_; uint8_t v_quasiPatternApprox_3699_; uint8_t v_constApprox_3700_; uint8_t v_isDefEqStuckEx_3701_; uint8_t v_unificationHints_3702_; uint8_t v_proofIrrelevance_3703_; uint8_t v_assignSyntheticOpaque_3704_; uint8_t v_offsetCnstrs_3705_; uint8_t v_transparency_3706_; uint8_t v_univApprox_3707_; uint8_t v_zetaUnused_3708_; uint8_t v_canUnfoldPredicateConfig_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3740_; 
v___x_3696_ = l_Lean_Meta_Context_config(v___y_3690_);
v_foApprox_3697_ = lean_ctor_get_uint8(v___x_3696_, 0);
v_ctxApprox_3698_ = lean_ctor_get_uint8(v___x_3696_, 1);
v_quasiPatternApprox_3699_ = lean_ctor_get_uint8(v___x_3696_, 2);
v_constApprox_3700_ = lean_ctor_get_uint8(v___x_3696_, 3);
v_isDefEqStuckEx_3701_ = lean_ctor_get_uint8(v___x_3696_, 4);
v_unificationHints_3702_ = lean_ctor_get_uint8(v___x_3696_, 5);
v_proofIrrelevance_3703_ = lean_ctor_get_uint8(v___x_3696_, 6);
v_assignSyntheticOpaque_3704_ = lean_ctor_get_uint8(v___x_3696_, 7);
v_offsetCnstrs_3705_ = lean_ctor_get_uint8(v___x_3696_, 8);
v_transparency_3706_ = lean_ctor_get_uint8(v___x_3696_, 9);
v_univApprox_3707_ = lean_ctor_get_uint8(v___x_3696_, 11);
v_zetaUnused_3708_ = lean_ctor_get_uint8(v___x_3696_, 17);
v_canUnfoldPredicateConfig_3709_ = lean_ctor_get_uint8(v___x_3696_, 19);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3711_ = v___x_3696_;
v_isShared_3712_ = v_isSharedCheck_3740_;
goto v_resetjp_3710_;
}
else
{
lean_dec(v___x_3696_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3740_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
uint8_t v___x_3713_; uint8_t v___x_3714_; uint8_t v___x_3715_; lean_object* v___x_3717_; 
v___x_3713_ = 1;
v___x_3714_ = 0;
v___x_3715_ = 2;
if (v_isShared_3712_ == 0)
{
v___x_3717_ = v___x_3711_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 0, v_foApprox_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 1, v_ctxApprox_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 2, v_quasiPatternApprox_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 3, v_constApprox_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 4, v_isDefEqStuckEx_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 5, v_unificationHints_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 6, v_proofIrrelevance_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 7, v_assignSyntheticOpaque_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 8, v_offsetCnstrs_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 9, v_transparency_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 11, v_univApprox_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 17, v_zetaUnused_3708_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 19, v_canUnfoldPredicateConfig_3709_);
v___x_3717_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
uint8_t v_trackZetaDelta_3718_; lean_object* v_zetaDeltaSet_3719_; lean_object* v_lctx_3720_; lean_object* v_localInstances_3721_; lean_object* v_defEqCtx_x3f_3722_; lean_object* v_synthPendingDepth_3723_; lean_object* v_customCanUnfoldPredicate_x3f_3724_; uint8_t v_univApprox_3725_; uint8_t v_inTypeClassResolution_3726_; uint8_t v_cacheInferType_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3737_; 
lean_ctor_set_uint8(v___x_3717_, 10, v___x_3714_);
lean_ctor_set_uint8(v___x_3717_, 12, v___x_3713_);
lean_ctor_set_uint8(v___x_3717_, 13, v___x_3713_);
lean_ctor_set_uint8(v___x_3717_, 14, v___x_3715_);
lean_ctor_set_uint8(v___x_3717_, 15, v___x_3713_);
lean_ctor_set_uint8(v___x_3717_, 16, v___x_3713_);
lean_ctor_set_uint8(v___x_3717_, 18, v___x_3713_);
v_trackZetaDelta_3718_ = lean_ctor_get_uint8(v___y_3690_, sizeof(void*)*7);
v_zetaDeltaSet_3719_ = lean_ctor_get(v___y_3690_, 1);
v_lctx_3720_ = lean_ctor_get(v___y_3690_, 2);
v_localInstances_3721_ = lean_ctor_get(v___y_3690_, 3);
v_defEqCtx_x3f_3722_ = lean_ctor_get(v___y_3690_, 4);
v_synthPendingDepth_3723_ = lean_ctor_get(v___y_3690_, 5);
v_customCanUnfoldPredicate_x3f_3724_ = lean_ctor_get(v___y_3690_, 6);
v_univApprox_3725_ = lean_ctor_get_uint8(v___y_3690_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3726_ = lean_ctor_get_uint8(v___y_3690_, sizeof(void*)*7 + 2);
v_cacheInferType_3727_ = lean_ctor_get_uint8(v___y_3690_, sizeof(void*)*7 + 3);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___y_3690_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; 
v_unused_3738_ = lean_ctor_get(v___y_3690_, 0);
lean_dec(v_unused_3738_);
v___x_3729_ = v___y_3690_;
v_isShared_3730_ = v_isSharedCheck_3737_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3724_);
lean_inc(v_synthPendingDepth_3723_);
lean_inc(v_defEqCtx_x3f_3722_);
lean_inc(v_localInstances_3721_);
lean_inc(v_lctx_3720_);
lean_inc(v_zetaDeltaSet_3719_);
lean_dec(v___y_3690_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3737_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
uint64_t v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
v___x_3731_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3717_);
v___x_3732_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3732_, 0, v___x_3717_);
lean_ctor_set_uint64(v___x_3732_, sizeof(void*)*1, v___x_3731_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3732_);
v___x_3734_ = v___x_3729_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_zetaDeltaSet_3719_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v_lctx_3720_);
lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_localInstances_3721_);
lean_ctor_set(v_reuseFailAlloc_3736_, 4, v_defEqCtx_x3f_3722_);
lean_ctor_set(v_reuseFailAlloc_3736_, 5, v_synthPendingDepth_3723_);
lean_ctor_set(v_reuseFailAlloc_3736_, 6, v_customCanUnfoldPredicate_x3f_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, sizeof(void*)*7, v_trackZetaDelta_3718_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, sizeof(void*)*7 + 1, v_univApprox_3725_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3736_, sizeof(void*)*7 + 3, v_cacheInferType_3727_);
v___x_3734_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; 
v___x_3735_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3689_, v___x_3734_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec_ref(v___x_3734_);
return v___x_3735_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v___y_3770_; lean_object* v_toCold_3787_; lean_object* v_currRecDepth_3788_; lean_object* v_ref_3789_; uint16_t v_optionFlags_3790_; uint8_t v_suppressElabErrors_3791_; uint8_t v_isRecordingDeps_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3832_; 
v_toCold_3787_ = lean_ctor_get(v_a_3766_, 0);
v_currRecDepth_3788_ = lean_ctor_get(v_a_3766_, 1);
v_ref_3789_ = lean_ctor_get(v_a_3766_, 2);
v_optionFlags_3790_ = lean_ctor_get_uint16(v_a_3766_, sizeof(void*)*3);
v_suppressElabErrors_3791_ = lean_ctor_get_uint8(v_a_3766_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3792_ = lean_ctor_get_uint8(v_a_3766_, sizeof(void*)*3 + 3);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3794_ = v_a_3766_;
v_isShared_3795_ = v_isSharedCheck_3832_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_ref_3789_);
lean_inc(v_currRecDepth_3788_);
lean_inc(v_toCold_3787_);
lean_dec(v_a_3766_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3832_;
goto v_resetjp_3793_;
}
v___jp_3769_:
{
if (lean_obj_tag(v___y_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
v_a_3771_ = lean_ctor_get(v___y_3770_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___y_3770_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___y_3770_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___y_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_a_3779_ = lean_ctor_get(v___y_3770_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___y_3770_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___y_3770_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___y_3770_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
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
v_resetjp_3793_:
{
lean_object* v_maxRecDepth_3796_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_maxRecDepth_3796_ = lean_ctor_get(v_toCold_3787_, 3);
v___x_3828_ = lean_unsigned_to_nat(0u);
v___x_3829_ = lean_nat_dec_eq(v_maxRecDepth_3796_, v___x_3828_);
if (v___x_3829_ == 0)
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_nat_dec_eq(v_currRecDepth_3788_, v_maxRecDepth_3796_);
if (v___x_3830_ == 0)
{
goto v___jp_3797_;
}
else
{
lean_object* v___x_3831_; 
lean_del_object(v___x_3794_);
lean_dec(v_currRecDepth_3788_);
lean_dec_ref(v_toCold_3787_);
lean_dec(v_a_3767_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec_ref(v_e_3763_);
v___x_3831_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3789_);
return v___x_3831_;
}
}
else
{
goto v___jp_3797_;
}
v___jp_3797_:
{
lean_object* v___x_3798_; uint8_t v_transparency_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3803_; 
v___x_3798_ = l_Lean_Meta_Context_config(v_a_3764_);
v_transparency_3799_ = lean_ctor_get_uint8(v___x_3798_, 9);
lean_dec_ref(v___x_3798_);
v___x_3800_ = lean_unsigned_to_nat(1u);
v___x_3801_ = lean_nat_add(v_currRecDepth_3788_, v___x_3800_);
lean_dec(v_currRecDepth_3788_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 1, v___x_3801_);
v___x_3803_ = v___x_3794_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_toCold_3787_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v_ref_3789_);
lean_ctor_set_uint16(v_reuseFailAlloc_3827_, sizeof(void*)*3, v_optionFlags_3790_);
lean_ctor_set_uint8(v_reuseFailAlloc_3827_, sizeof(void*)*3 + 2, v_suppressElabErrors_3791_);
lean_ctor_set_uint8(v_reuseFailAlloc_3827_, sizeof(void*)*3 + 3, v_isRecordingDeps_3792_);
v___x_3803_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
uint8_t v___x_3804_; uint8_t v___x_3805_; 
v___x_3804_ = 1;
v___x_3805_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3799_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3763_, v_a_3764_, v_a_3765_, v___x_3803_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v___x_3803_);
lean_dec(v_a_3765_);
v___y_3770_ = v___x_3806_;
goto v___jp_3769_;
}
else
{
lean_object* v_keyedConfig_3807_; uint8_t v_trackZetaDelta_3808_; lean_object* v_zetaDeltaSet_3809_; lean_object* v_lctx_3810_; lean_object* v_localInstances_3811_; lean_object* v_defEqCtx_x3f_3812_; lean_object* v_synthPendingDepth_3813_; lean_object* v_customCanUnfoldPredicate_x3f_3814_; uint8_t v_univApprox_3815_; uint8_t v_inTypeClassResolution_3816_; uint8_t v_cacheInferType_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3826_; 
v_keyedConfig_3807_ = lean_ctor_get(v_a_3764_, 0);
v_trackZetaDelta_3808_ = lean_ctor_get_uint8(v_a_3764_, sizeof(void*)*7);
v_zetaDeltaSet_3809_ = lean_ctor_get(v_a_3764_, 1);
v_lctx_3810_ = lean_ctor_get(v_a_3764_, 2);
v_localInstances_3811_ = lean_ctor_get(v_a_3764_, 3);
v_defEqCtx_x3f_3812_ = lean_ctor_get(v_a_3764_, 4);
v_synthPendingDepth_3813_ = lean_ctor_get(v_a_3764_, 5);
v_customCanUnfoldPredicate_x3f_3814_ = lean_ctor_get(v_a_3764_, 6);
v_univApprox_3815_ = lean_ctor_get_uint8(v_a_3764_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3816_ = lean_ctor_get_uint8(v_a_3764_, sizeof(void*)*7 + 2);
v_cacheInferType_3817_ = lean_ctor_get_uint8(v_a_3764_, sizeof(void*)*7 + 3);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_a_3764_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3819_ = v_a_3764_;
v_isShared_3820_ = v_isSharedCheck_3826_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3814_);
lean_inc(v_synthPendingDepth_3813_);
lean_inc(v_defEqCtx_x3f_3812_);
lean_inc(v_localInstances_3811_);
lean_inc(v_lctx_3810_);
lean_inc(v_zetaDeltaSet_3809_);
lean_inc(v_keyedConfig_3807_);
lean_dec(v_a_3764_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3826_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3821_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3804_, v_keyedConfig_3807_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3821_);
v___x_3823_ = v___x_3819_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_zetaDeltaSet_3809_);
lean_ctor_set(v_reuseFailAlloc_3825_, 2, v_lctx_3810_);
lean_ctor_set(v_reuseFailAlloc_3825_, 3, v_localInstances_3811_);
lean_ctor_set(v_reuseFailAlloc_3825_, 4, v_defEqCtx_x3f_3812_);
lean_ctor_set(v_reuseFailAlloc_3825_, 5, v_synthPendingDepth_3813_);
lean_ctor_set(v_reuseFailAlloc_3825_, 6, v_customCanUnfoldPredicate_x3f_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*7, v_trackZetaDelta_3808_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*7 + 1, v_univApprox_3815_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3816_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*7 + 3, v_cacheInferType_3817_);
v___x_3823_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3763_, v___x_3823_, v_a_3765_, v___x_3803_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v___x_3803_);
lean_dec(v_a_3765_);
v___y_3770_ = v___x_3824_;
goto v___jp_3769_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = lean_infer_type(v_e_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
return v_res_3839_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3840_){
_start:
{
switch(lean_obj_tag(v_x_3840_))
{
case 0:
{
uint8_t v___x_3841_; 
v___x_3841_ = 1;
return v___x_3841_;
}
case 2:
{
lean_object* v_a_3842_; lean_object* v_a_3843_; uint8_t v___x_3844_; 
v_a_3842_ = lean_ctor_get(v_x_3840_, 0);
v_a_3843_ = lean_ctor_get(v_x_3840_, 1);
v___x_3844_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3842_);
if (v___x_3844_ == 0)
{
return v___x_3844_;
}
else
{
v_x_3840_ = v_a_3843_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3846_; 
v_a_3846_ = lean_ctor_get(v_x_3840_, 1);
v_x_3840_ = v_a_3846_;
goto _start;
}
default: 
{
uint8_t v___x_3848_; 
v___x_3848_ = 0;
return v___x_3848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3849_){
_start:
{
uint8_t v_res_3850_; lean_object* v_r_3851_; 
v_res_3850_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3849_);
lean_dec(v_x_3849_);
v_r_3851_ = lean_box(v_res_3850_);
return v_r_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v___x_3855_; lean_object* v_mctx_3856_; lean_object* v___x_3857_; lean_object* v_fst_3858_; lean_object* v_snd_3859_; lean_object* v___x_3860_; lean_object* v_cache_3861_; lean_object* v_zetaDeltaFVarIds_3862_; lean_object* v_postponed_3863_; lean_object* v_diag_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3873_; 
v___x_3855_ = lean_st_ref_get(v___y_3853_);
v_mctx_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc_ref(v_mctx_3856_);
lean_dec(v___x_3855_);
v___x_3857_ = lean_instantiate_level_mvars(v_mctx_3856_, v_l_3852_);
v_fst_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_fst_3858_);
v_snd_3859_ = lean_ctor_get(v___x_3857_, 1);
lean_inc(v_snd_3859_);
lean_dec_ref(v___x_3857_);
v___x_3860_ = lean_st_ref_take(v___y_3853_);
v_cache_3861_ = lean_ctor_get(v___x_3860_, 1);
v_zetaDeltaFVarIds_3862_ = lean_ctor_get(v___x_3860_, 2);
v_postponed_3863_ = lean_ctor_get(v___x_3860_, 3);
v_diag_3864_ = lean_ctor_get(v___x_3860_, 4);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; 
v_unused_3874_ = lean_ctor_get(v___x_3860_, 0);
lean_dec(v_unused_3874_);
v___x_3866_ = v___x_3860_;
v_isShared_3867_ = v_isSharedCheck_3873_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_diag_3864_);
lean_inc(v_postponed_3863_);
lean_inc(v_zetaDeltaFVarIds_3862_);
lean_inc(v_cache_3861_);
lean_dec(v___x_3860_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3873_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v_fst_3858_);
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_fst_3858_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_cache_3861_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_zetaDeltaFVarIds_3862_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_postponed_3863_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_diag_3864_);
v___x_3869_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_st_ref_put(v___y_3853_, v___x_3869_);
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v_snd_3859_);
return v___x_3871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3875_, v___y_3876_);
lean_dec(v___y_3876_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3879_, v___y_3881_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3893_, lean_object* v_x_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
switch(lean_obj_tag(v_x_3893_))
{
case 3:
{
lean_object* v_u_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; 
v_u_3904_ = lean_ctor_get(v_x_3893_, 0);
lean_inc(v_u_3904_);
lean_dec_ref_known(v_x_3893_, 1);
v___x_3905_ = lean_unsigned_to_nat(0u);
v___x_3906_ = lean_nat_dec_eq(v_x_3894_, v___x_3905_);
lean_dec(v_x_3894_);
if (v___x_3906_ == 0)
{
lean_dec(v_u_3904_);
goto v___jp_3900_;
}
else
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3904_, v_a_3896_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3918_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3918_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
uint8_t v___x_3912_; uint8_t v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
v___x_3912_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3908_);
lean_dec(v_a_3908_);
v___x_3913_ = l_Lean_Bool_toLBool(v___x_3912_);
v___x_3914_ = lean_box(v___x_3913_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3914_);
v___x_3916_ = v___x_3910_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_a_3919_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3907_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3907_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3927_; lean_object* v_zero_3928_; uint8_t v_isZero_3929_; 
v_body_3927_ = lean_ctor_get(v_x_3893_, 2);
lean_inc_ref(v_body_3927_);
lean_dec_ref_known(v_x_3893_, 3);
v_zero_3928_ = lean_unsigned_to_nat(0u);
v_isZero_3929_ = lean_nat_dec_eq(v_x_3894_, v_zero_3928_);
if (v_isZero_3929_ == 1)
{
uint8_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec_ref(v_body_3927_);
lean_dec(v_x_3894_);
v___x_3930_ = 0;
v___x_3931_ = lean_box(v___x_3930_);
v___x_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
return v___x_3932_;
}
else
{
lean_object* v_one_3933_; lean_object* v_n_3934_; 
v_one_3933_ = lean_unsigned_to_nat(1u);
v_n_3934_ = lean_nat_sub(v_x_3894_, v_one_3933_);
lean_dec(v_x_3894_);
v_x_3893_ = v_body_3927_;
v_x_3894_ = v_n_3934_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3936_; 
v_body_3936_ = lean_ctor_get(v_x_3893_, 3);
lean_inc_ref(v_body_3936_);
lean_dec_ref_known(v_x_3893_, 4);
v_x_3893_ = v_body_3936_;
goto _start;
}
case 10:
{
lean_object* v_expr_3938_; 
v_expr_3938_ = lean_ctor_get(v_x_3893_, 1);
lean_inc_ref(v_expr_3938_);
lean_dec_ref_known(v_x_3893_, 2);
v_x_3893_ = v_expr_3938_;
goto _start;
}
default: 
{
lean_dec(v_x_3894_);
lean_dec_ref(v_x_3893_);
goto v___jp_3900_;
}
}
v___jp_3900_:
{
uint8_t v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = 2;
v___x_3902_ = lean_box(v___x_3901_);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3940_, lean_object* v_x_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3940_, v_x_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3948_, lean_object* v_x_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
switch(lean_obj_tag(v_x_3948_))
{
case 4:
{
lean_object* v_declName_3955_; lean_object* v_us_3956_; lean_object* v___x_3957_; 
v_declName_3955_ = lean_ctor_get(v_x_3948_, 0);
lean_inc(v_declName_3955_);
v_us_3956_ = lean_ctor_get(v_x_3948_, 1);
lean_inc(v_us_3956_);
lean_dec_ref_known(v_x_3948_, 2);
v___x_3957_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3955_, v_us_3956_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3958_, v_x_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
return v___x_3959_;
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v_x_3949_);
v_a_3960_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3957_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3957_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3968_; lean_object* v___x_3969_; 
v_fvarId_3968_ = lean_ctor_get(v_x_3948_, 0);
lean_inc(v_fvarId_3968_);
lean_dec_ref_known(v_x_3948_, 1);
v___x_3969_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3968_, v_a_3950_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v___x_3971_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3970_, v_x_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
return v___x_3971_;
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_x_3949_);
v_a_3972_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3969_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3969_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3980_; lean_object* v___x_3981_; 
v_mvarId_3980_ = lean_ctor_get(v_x_3948_, 0);
lean_inc(v_mvarId_3980_);
lean_dec_ref_known(v_x_3948_, 1);
v___x_3981_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3980_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3982_, v_x_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_);
return v___x_3983_;
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v_x_3949_);
v_a_3984_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3981_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3981_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
case 5:
{
lean_object* v_fn_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v_fn_3992_ = lean_ctor_get(v_x_3948_, 0);
lean_inc_ref(v_fn_3992_);
lean_dec_ref_known(v_x_3948_, 2);
v___x_3993_ = lean_unsigned_to_nat(1u);
v___x_3994_ = lean_nat_add(v_x_3949_, v___x_3993_);
lean_dec(v_x_3949_);
v_x_3948_ = v_fn_3992_;
v_x_3949_ = v___x_3994_;
goto _start;
}
case 10:
{
lean_object* v_expr_3996_; 
v_expr_3996_ = lean_ctor_get(v_x_3948_, 1);
lean_inc_ref(v_expr_3996_);
lean_dec_ref_known(v_x_3948_, 2);
v_x_3948_ = v_expr_3996_;
goto _start;
}
case 8:
{
lean_object* v_body_3998_; 
v_body_3998_ = lean_ctor_get(v_x_3948_, 3);
lean_inc_ref(v_body_3998_);
lean_dec_ref_known(v_x_3948_, 4);
v_x_3948_ = v_body_3998_;
goto _start;
}
case 6:
{
lean_object* v_body_4000_; lean_object* v_zero_4001_; uint8_t v_isZero_4002_; 
v_body_4000_ = lean_ctor_get(v_x_3948_, 2);
lean_inc_ref(v_body_4000_);
lean_dec_ref_known(v_x_3948_, 3);
v_zero_4001_ = lean_unsigned_to_nat(0u);
v_isZero_4002_ = lean_nat_dec_eq(v_x_3949_, v_zero_4001_);
if (v_isZero_4002_ == 1)
{
uint8_t v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_dec_ref(v_body_4000_);
lean_dec(v_x_3949_);
v___x_4003_ = 0;
v___x_4004_ = lean_box(v___x_4003_);
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
return v___x_4005_;
}
else
{
lean_object* v_one_4006_; lean_object* v_n_4007_; 
v_one_4006_ = lean_unsigned_to_nat(1u);
v_n_4007_ = lean_nat_sub(v_x_3949_, v_one_4006_);
lean_dec(v_x_3949_);
v_x_3948_ = v_body_4000_;
v_x_3949_ = v_n_4007_;
goto _start;
}
}
default: 
{
uint8_t v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_dec(v_x_3949_);
lean_dec_ref(v_x_3948_);
v___x_4009_ = 2;
v___x_4010_ = lean_box(v___x_4009_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4012_, lean_object* v_x_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4012_, v_x_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
switch(lean_obj_tag(v_x_4020_))
{
case 1:
{
lean_object* v_fvarId_4026_; lean_object* v___x_4027_; 
v_fvarId_4026_ = lean_ctor_get(v_x_4020_, 0);
lean_inc(v_fvarId_4026_);
lean_dec_ref_known(v_x_4020_, 1);
v___x_4027_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4026_, v_a_4021_, v_a_4023_, v_a_4024_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = lean_unsigned_to_nat(0u);
v___x_4030_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4028_, v___x_4029_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
return v___x_4030_;
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
v_a_4031_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4027_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4027_);
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
case 2:
{
lean_object* v_mvarId_4039_; lean_object* v___x_4040_; 
v_mvarId_4039_ = lean_ctor_get(v_x_4020_, 0);
lean_inc(v_mvarId_4039_);
lean_dec_ref_known(v_x_4020_, 1);
v___x_4040_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4039_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4041_, v___x_4042_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
return v___x_4043_;
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4040_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4040_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
case 3:
{
uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_dec_ref_known(v_x_4020_, 1);
v___x_4052_ = 0;
v___x_4053_ = lean_box(v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
return v___x_4054_;
}
case 4:
{
lean_object* v_declName_4055_; lean_object* v_us_4056_; lean_object* v___x_4057_; 
v_declName_4055_ = lean_ctor_get(v_x_4020_, 0);
lean_inc(v_declName_4055_);
v_us_4056_ = lean_ctor_get(v_x_4020_, 1);
lean_inc(v_us_4056_);
lean_dec_ref_known(v_x_4020_, 2);
v___x_4057_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4055_, v_us_4056_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___x_4057_, 1);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4058_, v___x_4059_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
return v___x_4060_;
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
v_a_4061_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4057_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4057_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
case 5:
{
lean_object* v_fn_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_fn_4069_ = lean_ctor_get(v_x_4020_, 0);
lean_inc_ref(v_fn_4069_);
lean_dec_ref_known(v_x_4020_, 2);
v___x_4070_ = lean_unsigned_to_nat(1u);
v___x_4071_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4069_, v___x_4070_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
return v___x_4071_;
}
case 6:
{
uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
lean_dec_ref_known(v_x_4020_, 3);
v___x_4072_ = 0;
v___x_4073_ = lean_box(v___x_4072_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
case 7:
{
lean_object* v_body_4075_; 
v_body_4075_ = lean_ctor_get(v_x_4020_, 2);
lean_inc_ref(v_body_4075_);
lean_dec_ref_known(v_x_4020_, 3);
v_x_4020_ = v_body_4075_;
goto _start;
}
case 8:
{
lean_object* v_body_4077_; 
v_body_4077_ = lean_ctor_get(v_x_4020_, 3);
lean_inc_ref(v_body_4077_);
lean_dec_ref_known(v_x_4020_, 4);
v_x_4020_ = v_body_4077_;
goto _start;
}
case 9:
{
uint8_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
lean_dec_ref_known(v_x_4020_, 1);
v___x_4079_ = 0;
v___x_4080_ = lean_box(v___x_4079_);
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
case 10:
{
lean_object* v_expr_4082_; 
v_expr_4082_ = lean_ctor_get(v_x_4020_, 1);
lean_inc_ref(v_expr_4082_);
lean_dec_ref_known(v_x_4020_, 2);
v_x_4020_ = v_expr_4082_;
goto _start;
}
default: 
{
uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
lean_dec_ref(v_x_4020_);
v___x_4084_ = 2;
v___x_4085_ = lean_box(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_Meta_isPropQuick(v_x_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v___x_4100_; 
lean_inc_ref(v_e_4094_);
v___x_4100_ = l_Lean_Meta_isPropQuick(v_e_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4157_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4157_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4157_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
uint8_t v___x_4105_; 
v___x_4105_ = lean_unbox(v_a_4101_);
lean_dec(v_a_4101_);
switch(v___x_4105_)
{
case 0:
{
uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
lean_dec_ref(v_e_4094_);
v___x_4106_ = 0;
v___x_4107_ = lean_box(v___x_4106_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4107_);
v___x_4109_ = v___x_4103_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
case 1:
{
uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
lean_dec_ref(v_e_4094_);
v___x_4111_ = 1;
v___x_4112_ = lean_box(v___x_4111_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4112_);
v___x_4114_ = v___x_4103_;
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
default: 
{
lean_object* v___x_4116_; 
lean_del_object(v___x_4103_);
lean_inc(v_a_4098_);
lean_inc_ref(v_a_4097_);
lean_inc(v_a_4096_);
lean_inc_ref(v_a_4095_);
v___x_4116_ = lean_infer_type(v_e_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref_known(v___x_4116_, 1);
v___x_4118_ = l_Lean_Meta_whnfD(v_a_4117_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4140_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4140_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4140_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
if (lean_obj_tag(v_a_4119_) == 3)
{
lean_object* v_u_4123_; lean_object* v___x_4124_; lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4134_; 
lean_del_object(v___x_4121_);
v_u_4123_ = lean_ctor_get(v_a_4119_, 0);
lean_inc(v_u_4123_);
lean_dec_ref_known(v_a_4119_, 1);
v___x_4124_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4123_, v_a_4096_);
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4127_ = v___x_4124_;
v_isShared_4128_ = v_isSharedCheck_4134_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4134_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
uint8_t v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4132_; 
v___x_4129_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4125_);
lean_dec(v_a_4125_);
v___x_4130_ = lean_box(v___x_4129_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 0, v___x_4130_);
v___x_4132_ = v___x_4127_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
else
{
uint8_t v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
lean_dec(v_a_4119_);
v___x_4135_ = 0;
v___x_4136_ = lean_box(v___x_4135_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4136_);
v___x_4138_ = v___x_4121_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
v_a_4141_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4118_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4118_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_a_4149_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4116_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4116_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec_ref(v_e_4094_);
v_a_4158_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4100_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4100_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Meta_isProp(v_e_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4173_){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = lean_obj_tag_nat(v_x_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4175_);
lean_dec(v_x_4175_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4177_, lean_object* v_k_4178_){
_start:
{
if (lean_obj_tag(v_t_4177_) == 3)
{
lean_object* v_idx_4179_; lean_object* v_numArgs_4180_; lean_object* v___x_4181_; 
v_idx_4179_ = lean_ctor_get(v_t_4177_, 0);
lean_inc(v_idx_4179_);
v_numArgs_4180_ = lean_ctor_get(v_t_4177_, 1);
lean_inc(v_numArgs_4180_);
lean_dec_ref_known(v_t_4177_, 2);
v___x_4181_ = lean_apply_2(v_k_4178_, v_idx_4179_, v_numArgs_4180_);
return v___x_4181_;
}
else
{
lean_dec(v_t_4177_);
return v_k_4178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4182_, lean_object* v_ctorIdx_4183_, lean_object* v_t_4184_, lean_object* v_h_4185_, lean_object* v_k_4186_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4184_, v_k_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4188_, lean_object* v_ctorIdx_4189_, lean_object* v_t_4190_, lean_object* v_h_4191_, lean_object* v_k_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4188_, v_ctorIdx_4189_, v_t_4190_, v_h_4191_, v_k_4192_);
lean_dec(v_ctorIdx_4189_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4194_, lean_object* v_false_4195_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4194_, v_false_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4197_, lean_object* v_t_4198_, lean_object* v_h_4199_, lean_object* v_false_4200_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4198_, v_false_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4202_, lean_object* v_true_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4202_, v_true_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4205_, lean_object* v_t_4206_, lean_object* v_h_4207_, lean_object* v_true_4208_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4206_, v_true_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4210_, lean_object* v_undef_4211_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4210_, v_undef_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4213_, lean_object* v_t_4214_, lean_object* v_h_4215_, lean_object* v_undef_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4214_, v_undef_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4218_, lean_object* v_bvar_4219_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4218_, v_bvar_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4221_, lean_object* v_t_4222_, lean_object* v_h_4223_, lean_object* v_bvar_4224_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4222_, v_bvar_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4226_){
_start:
{
switch(v_x_4226_)
{
case 0:
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_box(0);
return v___x_4227_;
}
case 1:
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_box(1);
return v___x_4228_;
}
default: 
{
lean_object* v___x_4229_; 
v___x_4229_ = lean_box(2);
return v___x_4229_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4230_){
_start:
{
uint8_t v_x_25__boxed_4231_; lean_object* v_res_4232_; 
v_x_25__boxed_4231_ = lean_unbox(v_x_4230_);
v_res_4232_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4231_);
return v_res_4232_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4233_){
_start:
{
switch(lean_obj_tag(v_x_4233_))
{
case 0:
{
uint8_t v___x_4234_; 
v___x_4234_ = 0;
return v___x_4234_;
}
case 1:
{
uint8_t v___x_4235_; 
v___x_4235_ = 1;
return v___x_4235_;
}
default: 
{
uint8_t v___x_4236_; 
v___x_4236_ = 2;
return v___x_4236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4237_){
_start:
{
uint8_t v_res_4238_; lean_object* v_r_4239_; 
v_res_4238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4237_);
lean_dec(v_x_4237_);
v_r_4239_ = lean_box(v_res_4238_);
return v_r_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4241_, lean_object* v_numArgs_4242_){
_start:
{
switch(lean_obj_tag(v_e_4241_))
{
case 3:
{
lean_object* v_u_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; 
v_u_4243_ = lean_ctor_get(v_e_4241_, 0);
v___x_4244_ = lean_unsigned_to_nat(0u);
v___x_4245_ = lean_nat_dec_eq(v_numArgs_4242_, v___x_4244_);
lean_dec(v_numArgs_4242_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
v___x_4246_ = lean_box(2);
return v___x_4246_;
}
else
{
uint8_t v___x_4247_; 
v___x_4247_ = l_Lean_Level_isNeverZero(v_u_4243_);
if (v___x_4247_ == 0)
{
uint8_t v___x_4248_; 
v___x_4248_ = l_Lean_Level_isZero(v_u_4243_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_box(2);
return v___x_4249_;
}
else
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_box(1);
return v___x_4250_;
}
}
else
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_box(0);
return v___x_4251_;
}
}
}
case 7:
{
lean_object* v_body_4252_; lean_object* v_zero_4253_; uint8_t v_isZero_4254_; 
v_body_4252_ = lean_ctor_get(v_e_4241_, 2);
v_zero_4253_ = lean_unsigned_to_nat(0u);
v_isZero_4254_ = lean_nat_dec_eq(v_numArgs_4242_, v_zero_4253_);
if (v_isZero_4254_ == 0)
{
lean_object* v_one_4255_; lean_object* v_n_4256_; 
v_one_4255_ = lean_unsigned_to_nat(1u);
v_n_4256_ = lean_nat_sub(v_numArgs_4242_, v_one_4255_);
lean_dec(v_numArgs_4242_);
v_e_4241_ = v_body_4252_;
v_numArgs_4242_ = v_n_4256_;
goto _start;
}
else
{
lean_object* v___x_4258_; 
lean_dec(v_numArgs_4242_);
v___x_4258_ = lean_box(2);
return v___x_4258_;
}
}
case 10:
{
lean_object* v_expr_4259_; 
v_expr_4259_ = lean_ctor_get(v_e_4241_, 1);
v_e_4241_ = v_expr_4259_;
goto _start;
}
case 5:
{
lean_object* v_fn_4261_; 
v_fn_4261_ = lean_ctor_get(v_e_4241_, 0);
if (lean_obj_tag(v_fn_4261_) == 4)
{
lean_object* v_declName_4262_; 
v_declName_4262_ = lean_ctor_get(v_fn_4261_, 0);
if (lean_obj_tag(v_declName_4262_) == 1)
{
lean_object* v_pre_4263_; 
v_pre_4263_ = lean_ctor_get(v_declName_4262_, 0);
if (lean_obj_tag(v_pre_4263_) == 0)
{
lean_object* v_arg_4264_; lean_object* v_str_4265_; lean_object* v___x_4266_; uint8_t v___x_4267_; 
v_arg_4264_ = lean_ctor_get(v_e_4241_, 1);
v_str_4265_ = lean_ctor_get(v_declName_4262_, 1);
v___x_4266_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4267_ = lean_string_dec_eq(v_str_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
lean_object* v___x_4268_; 
lean_dec(v_numArgs_4242_);
v___x_4268_ = lean_box(2);
return v___x_4268_;
}
else
{
v_e_4241_ = v_arg_4264_;
goto _start;
}
}
else
{
lean_object* v___x_4270_; 
lean_dec(v_numArgs_4242_);
v___x_4270_ = lean_box(2);
return v___x_4270_;
}
}
else
{
lean_object* v___x_4271_; 
lean_dec(v_numArgs_4242_);
v___x_4271_ = lean_box(2);
return v___x_4271_;
}
}
else
{
lean_object* v___x_4272_; 
lean_dec(v_numArgs_4242_);
v___x_4272_ = lean_box(2);
return v___x_4272_;
}
}
default: 
{
lean_object* v___x_4273_; 
lean_dec(v_numArgs_4242_);
v___x_4273_ = lean_box(2);
return v___x_4273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4274_, lean_object* v_numArgs_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4274_, v_numArgs_4275_);
lean_dec_ref(v_e_4274_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4277_, lean_object* v_binderType_4278_){
_start:
{
if (lean_obj_tag(v_r_4277_) == 3)
{
lean_object* v_idx_4279_; lean_object* v_numArgs_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4292_; 
v_idx_4279_ = lean_ctor_get(v_r_4277_, 0);
v_numArgs_4280_ = lean_ctor_get(v_r_4277_, 1);
v_isSharedCheck_4292_ = !lean_is_exclusive(v_r_4277_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4282_ = v_r_4277_;
v_isShared_4283_ = v_isSharedCheck_4292_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_numArgs_4280_);
lean_inc(v_idx_4279_);
lean_dec(v_r_4277_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4292_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v_zero_4284_; uint8_t v_isZero_4285_; 
v_zero_4284_ = lean_unsigned_to_nat(0u);
v_isZero_4285_ = lean_nat_dec_eq(v_idx_4279_, v_zero_4284_);
if (v_isZero_4285_ == 1)
{
lean_object* v___x_4286_; 
lean_del_object(v___x_4282_);
lean_dec(v_idx_4279_);
v___x_4286_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4278_, v_numArgs_4280_);
return v___x_4286_;
}
else
{
lean_object* v_one_4287_; lean_object* v_n_4288_; lean_object* v___x_4290_; 
v_one_4287_ = lean_unsigned_to_nat(1u);
v_n_4288_ = lean_nat_sub(v_idx_4279_, v_one_4287_);
lean_dec(v_idx_4279_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v_n_4288_);
v___x_4290_ = v___x_4282_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_n_4288_);
lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_numArgs_4280_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
return v_r_4277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4293_, lean_object* v_binderType_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4293_, v_binderType_4294_);
lean_dec_ref(v_binderType_4294_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4296_, lean_object* v_x_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_type_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; 
switch(lean_obj_tag(v_x_4296_))
{
case 7:
{
lean_object* v_binderType_4336_; lean_object* v_body_4337_; lean_object* v_zero_4338_; uint8_t v_isZero_4339_; 
v_binderType_4336_ = lean_ctor_get(v_x_4296_, 1);
v_body_4337_ = lean_ctor_get(v_x_4296_, 2);
v_zero_4338_ = lean_unsigned_to_nat(0u);
v_isZero_4339_ = lean_nat_dec_eq(v_x_4297_, v_zero_4338_);
if (v_isZero_4339_ == 1)
{
v_type_4304_ = v_x_4296_;
v___y_4305_ = v_a_4298_;
v___y_4306_ = v_a_4299_;
v___y_4307_ = v_a_4300_;
v___y_4308_ = v_a_4301_;
goto v___jp_4303_;
}
else
{
lean_object* v_one_4340_; lean_object* v_n_4341_; lean_object* v___x_4342_; 
lean_inc_ref(v_body_4337_);
lean_inc_ref(v_binderType_4336_);
lean_dec_ref_known(v_x_4296_, 3);
v_one_4340_ = lean_unsigned_to_nat(1u);
v_n_4341_ = lean_nat_sub(v_x_4297_, v_one_4340_);
v___x_4342_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4337_, v_n_4341_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
lean_dec(v_n_4341_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4351_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4351_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4351_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4347_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4343_, v_binderType_4336_);
lean_dec_ref(v_binderType_4336_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4347_);
v___x_4349_ = v___x_4345_;
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
lean_dec_ref(v_binderType_4336_);
return v___x_4342_;
}
}
}
case 8:
{
lean_object* v_type_4352_; lean_object* v_body_4353_; lean_object* v___x_4354_; 
v_type_4352_ = lean_ctor_get(v_x_4296_, 1);
lean_inc_ref(v_type_4352_);
v_body_4353_ = lean_ctor_get(v_x_4296_, 3);
lean_inc_ref(v_body_4353_);
lean_dec_ref_known(v_x_4296_, 4);
v___x_4354_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4353_, v_x_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4363_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4363_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4361_; 
v___x_4359_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4355_, v_type_4352_);
lean_dec_ref(v_type_4352_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4359_);
v___x_4361_ = v___x_4357_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4359_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
else
{
lean_dec_ref(v_type_4352_);
return v___x_4354_;
}
}
case 10:
{
lean_object* v_expr_4364_; 
v_expr_4364_ = lean_ctor_get(v_x_4296_, 1);
lean_inc_ref(v_expr_4364_);
lean_dec_ref_known(v_x_4296_, 2);
v_x_4296_ = v_expr_4364_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v_deBruijnIndex_4366_ = lean_ctor_get(v_x_4296_, 0);
lean_inc(v_deBruijnIndex_4366_);
lean_dec_ref_known(v_x_4296_, 1);
v___x_4367_ = lean_unsigned_to_nat(0u);
v___x_4368_ = lean_nat_dec_eq(v_x_4297_, v___x_4367_);
if (v___x_4368_ == 0)
{
lean_dec(v_deBruijnIndex_4366_);
goto v___jp_4333_;
}
else
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4369_, 0, v_deBruijnIndex_4366_);
lean_ctor_set(v___x_4369_, 1, v___x_4367_);
v___x_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
return v___x_4370_;
}
}
default: 
{
lean_object* v___x_4371_; uint8_t v___x_4372_; 
v___x_4371_ = lean_unsigned_to_nat(0u);
v___x_4372_ = lean_nat_dec_eq(v_x_4297_, v___x_4371_);
if (v___x_4372_ == 0)
{
lean_dec_ref(v_x_4296_);
goto v___jp_4333_;
}
else
{
v_type_4304_ = v_x_4296_;
v___y_4305_ = v_a_4298_;
v___y_4306_ = v_a_4299_;
v___y_4307_ = v_a_4300_;
v___y_4308_ = v_a_4301_;
goto v___jp_4303_;
}
}
}
v___jp_4303_:
{
lean_object* v___x_4309_; 
v___x_4309_ = l_Lean_Expr_getAppFn(v_type_4304_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_deBruijnIndex_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_deBruijnIndex_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_deBruijnIndex_4310_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4311_ = l_Lean_Expr_getAppNumArgs(v_type_4304_);
lean_dec_ref(v_type_4304_);
v___x_4312_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4312_, 0, v_deBruijnIndex_4310_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
return v___x_4313_;
}
else
{
lean_object* v___x_4314_; 
lean_dec_ref(v___x_4309_);
v___x_4314_ = l_Lean_Meta_isPropQuick(v_type_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4324_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4324_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4324_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
uint8_t v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4322_; 
v___x_4319_ = lean_unbox(v_a_4315_);
lean_dec(v_a_4315_);
v___x_4320_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4319_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 0, v___x_4320_);
v___x_4322_ = v___x_4317_;
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
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
v_a_4325_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4314_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4314_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
v___jp_4333_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = lean_box(2);
v___x_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
return v___x_4335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4373_, lean_object* v_x_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v_res_4380_; 
v_res_4380_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4373_, v_x_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
lean_dec(v_a_4378_);
lean_dec_ref(v_a_4377_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_x_4374_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4381_, lean_object* v_n_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4381_, v_n_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4398_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4391_ = v___x_4388_;
v_isShared_4392_ = v_isSharedCheck_4398_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4388_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4398_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4393_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4389_);
lean_dec(v_a_4389_);
v___x_4394_ = lean_box(v___x_4393_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 0, v___x_4394_);
v___x_4396_ = v___x_4391_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4394_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
v_a_4399_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4388_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4388_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4407_, lean_object* v_n_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4407_, v_n_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_);
lean_dec(v_a_4412_);
lean_dec_ref(v_a_4411_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_n_4408_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
switch(lean_obj_tag(v_x_4415_))
{
case 1:
{
lean_object* v_fvarId_4421_; lean_object* v___x_4422_; 
v_fvarId_4421_ = lean_ctor_get(v_x_4415_, 0);
lean_inc(v_fvarId_4421_);
lean_dec_ref_known(v_x_4415_, 1);
v___x_4422_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4421_, v_a_4416_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4423_);
lean_dec_ref_known(v___x_4422_, 1);
v___x_4424_ = lean_unsigned_to_nat(0u);
v___x_4425_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4423_, v___x_4424_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
return v___x_4425_;
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
v_a_4426_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4422_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4422_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4434_; lean_object* v___x_4435_; 
v_mvarId_4434_ = lean_ctor_get(v_x_4415_, 0);
lean_inc(v_mvarId_4434_);
lean_dec_ref_known(v_x_4415_, 1);
v___x_4435_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4434_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v___x_4437_ = lean_unsigned_to_nat(0u);
v___x_4438_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4436_, v___x_4437_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
return v___x_4438_;
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
v_a_4439_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4435_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4435_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
case 3:
{
uint8_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec_ref_known(v_x_4415_, 1);
v___x_4447_ = 0;
v___x_4448_ = lean_box(v___x_4447_);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
case 4:
{
lean_object* v_declName_4450_; lean_object* v_us_4451_; lean_object* v___x_4452_; 
v_declName_4450_ = lean_ctor_get(v_x_4415_, 0);
lean_inc(v_declName_4450_);
v_us_4451_ = lean_ctor_get(v_x_4415_, 1);
lean_inc(v_us_4451_);
lean_dec_ref_known(v_x_4415_, 2);
v___x_4452_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4450_, v_us_4451_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4452_, 1);
v___x_4454_ = lean_unsigned_to_nat(0u);
v___x_4455_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4453_, v___x_4454_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
return v___x_4455_;
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
v_a_4456_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4452_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4452_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
case 5:
{
lean_object* v_fn_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v_fn_4464_ = lean_ctor_get(v_x_4415_, 0);
lean_inc_ref(v_fn_4464_);
lean_dec_ref_known(v_x_4415_, 2);
v___x_4465_ = lean_unsigned_to_nat(1u);
v___x_4466_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4464_, v___x_4465_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
return v___x_4466_;
}
case 6:
{
lean_object* v_body_4467_; 
v_body_4467_ = lean_ctor_get(v_x_4415_, 2);
lean_inc_ref(v_body_4467_);
lean_dec_ref_known(v_x_4415_, 3);
v_x_4415_ = v_body_4467_;
goto _start;
}
case 7:
{
uint8_t v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_dec_ref_known(v_x_4415_, 3);
v___x_4469_ = 0;
v___x_4470_ = lean_box(v___x_4469_);
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
case 8:
{
lean_object* v_body_4472_; 
v_body_4472_ = lean_ctor_get(v_x_4415_, 3);
lean_inc_ref(v_body_4472_);
lean_dec_ref_known(v_x_4415_, 4);
v_x_4415_ = v_body_4472_;
goto _start;
}
case 9:
{
uint8_t v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_dec_ref_known(v_x_4415_, 1);
v___x_4474_ = 0;
v___x_4475_ = lean_box(v___x_4474_);
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
return v___x_4476_;
}
case 10:
{
lean_object* v_expr_4477_; 
v_expr_4477_ = lean_ctor_get(v_x_4415_, 1);
lean_inc_ref(v_expr_4477_);
lean_dec_ref_known(v_x_4415_, 2);
v_x_4415_ = v_expr_4477_;
goto _start;
}
default: 
{
uint8_t v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
lean_dec_ref(v_x_4415_);
v___x_4479_ = 2;
v___x_4480_ = lean_box(v___x_4479_);
v___x_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
return v___x_4481_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4482_, lean_object* v_x_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
switch(lean_obj_tag(v_x_4482_))
{
case 4:
{
lean_object* v_declName_4489_; lean_object* v_us_4490_; lean_object* v___x_4491_; 
v_declName_4489_ = lean_ctor_get(v_x_4482_, 0);
lean_inc(v_declName_4489_);
v_us_4490_ = lean_ctor_get(v_x_4482_, 1);
lean_inc(v_us_4490_);
lean_dec_ref_known(v_x_4482_, 2);
v___x_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4489_, v_us_4490_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4493_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___x_4493_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4492_, v_x_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec(v_x_4483_);
return v___x_4493_;
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_x_4483_);
v_a_4494_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4491_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4491_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4502_; lean_object* v___x_4503_; 
v_fvarId_4502_ = lean_ctor_get(v_x_4482_, 0);
lean_inc(v_fvarId_4502_);
lean_dec_ref_known(v_x_4482_, 1);
v___x_4503_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4502_, v_a_4484_, v_a_4486_, v_a_4487_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4505_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v___x_4503_, 1);
v___x_4505_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4504_, v_x_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec(v_x_4483_);
return v___x_4505_;
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v_x_4483_);
v_a_4506_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4503_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4503_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4514_; lean_object* v___x_4515_; 
v_mvarId_4514_ = lean_ctor_get(v_x_4482_, 0);
lean_inc(v_mvarId_4514_);
lean_dec_ref_known(v_x_4482_, 1);
v___x_4515_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4514_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4517_; 
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_a_4516_);
lean_dec_ref_known(v___x_4515_, 1);
v___x_4517_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4516_, v_x_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec(v_x_4483_);
return v___x_4517_;
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v_x_4483_);
v_a_4518_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4515_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4515_);
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
case 5:
{
lean_object* v_fn_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v_fn_4526_ = lean_ctor_get(v_x_4482_, 0);
lean_inc_ref(v_fn_4526_);
lean_dec_ref_known(v_x_4482_, 2);
v___x_4527_ = lean_unsigned_to_nat(1u);
v___x_4528_ = lean_nat_add(v_x_4483_, v___x_4527_);
lean_dec(v_x_4483_);
v_x_4482_ = v_fn_4526_;
v_x_4483_ = v___x_4528_;
goto _start;
}
case 10:
{
lean_object* v_expr_4530_; 
v_expr_4530_ = lean_ctor_get(v_x_4482_, 1);
lean_inc_ref(v_expr_4530_);
lean_dec_ref_known(v_x_4482_, 2);
v_x_4482_ = v_expr_4530_;
goto _start;
}
case 8:
{
lean_object* v_body_4532_; 
v_body_4532_ = lean_ctor_get(v_x_4482_, 3);
lean_inc_ref(v_body_4532_);
lean_dec_ref_known(v_x_4482_, 4);
v_x_4482_ = v_body_4532_;
goto _start;
}
case 6:
{
lean_object* v_body_4534_; lean_object* v_zero_4535_; uint8_t v_isZero_4536_; 
v_body_4534_ = lean_ctor_get(v_x_4482_, 2);
lean_inc_ref(v_body_4534_);
lean_dec_ref_known(v_x_4482_, 3);
v_zero_4535_ = lean_unsigned_to_nat(0u);
v_isZero_4536_ = lean_nat_dec_eq(v_x_4483_, v_zero_4535_);
if (v_isZero_4536_ == 1)
{
lean_object* v___x_4537_; 
lean_dec(v_x_4483_);
v___x_4537_ = l_Lean_Meta_isProofQuick(v_body_4534_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
return v___x_4537_;
}
else
{
lean_object* v_one_4538_; lean_object* v_n_4539_; 
v_one_4538_ = lean_unsigned_to_nat(1u);
v_n_4539_ = lean_nat_sub(v_x_4483_, v_one_4538_);
lean_dec(v_x_4483_);
v_x_4482_ = v_body_4534_;
v_x_4483_ = v_n_4539_;
goto _start;
}
}
default: 
{
uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec(v_x_4483_);
lean_dec_ref(v_x_4482_);
v___x_4541_ = 2;
v___x_4542_ = lean_box(v___x_4541_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4544_, lean_object* v_x_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4544_, v_x_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Meta_isProofQuick(v_x_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v___x_4565_; 
lean_inc_ref(v_e_4559_);
v___x_4565_ = l_Lean_Meta_isProofQuick(v_e_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4592_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4568_ = v___x_4565_;
v_isShared_4569_ = v_isSharedCheck_4592_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4565_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4592_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
uint8_t v___x_4570_; 
v___x_4570_ = lean_unbox(v_a_4566_);
lean_dec(v_a_4566_);
switch(v___x_4570_)
{
case 0:
{
uint8_t v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4574_; 
lean_dec_ref(v_e_4559_);
v___x_4571_ = 0;
v___x_4572_ = lean_box(v___x_4571_);
if (v_isShared_4569_ == 0)
{
lean_ctor_set(v___x_4568_, 0, v___x_4572_);
v___x_4574_ = v___x_4568_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
case 1:
{
uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4579_; 
lean_dec_ref(v_e_4559_);
v___x_4576_ = 1;
v___x_4577_ = lean_box(v___x_4576_);
if (v_isShared_4569_ == 0)
{
lean_ctor_set(v___x_4568_, 0, v___x_4577_);
v___x_4579_ = v___x_4568_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4577_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
default: 
{
lean_object* v___x_4581_; 
lean_del_object(v___x_4568_);
lean_inc(v_a_4563_);
lean_inc_ref(v_a_4562_);
lean_inc(v_a_4561_);
lean_inc_ref(v_a_4560_);
v___x_4581_ = lean_infer_type(v_e_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4583_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref_known(v___x_4581_, 1);
v___x_4583_ = l_Lean_Meta_isProp(v_a_4582_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
return v___x_4583_;
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
v_a_4584_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4581_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4581_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec_ref(v_e_4559_);
v_a_4593_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4565_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4565_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l_Lean_Meta_isProof(v_e_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4608_, lean_object* v_x_4609_){
_start:
{
switch(lean_obj_tag(v_x_4608_))
{
case 3:
{
lean_object* v___x_4615_; uint8_t v___x_4616_; 
v___x_4615_ = lean_unsigned_to_nat(0u);
v___x_4616_ = lean_nat_dec_eq(v_x_4609_, v___x_4615_);
lean_dec(v_x_4609_);
if (v___x_4616_ == 0)
{
goto v___jp_4611_;
}
else
{
uint8_t v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4617_ = 1;
v___x_4618_ = lean_box(v___x_4617_);
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
return v___x_4619_;
}
}
case 7:
{
lean_object* v_body_4620_; lean_object* v_zero_4621_; uint8_t v_isZero_4622_; 
v_body_4620_ = lean_ctor_get(v_x_4608_, 2);
v_zero_4621_ = lean_unsigned_to_nat(0u);
v_isZero_4622_ = lean_nat_dec_eq(v_x_4609_, v_zero_4621_);
if (v_isZero_4622_ == 1)
{
uint8_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
lean_dec(v_x_4609_);
v___x_4623_ = 0;
v___x_4624_ = lean_box(v___x_4623_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4624_);
return v___x_4625_;
}
else
{
lean_object* v_one_4626_; lean_object* v_n_4627_; 
v_one_4626_ = lean_unsigned_to_nat(1u);
v_n_4627_ = lean_nat_sub(v_x_4609_, v_one_4626_);
lean_dec(v_x_4609_);
v_x_4608_ = v_body_4620_;
v_x_4609_ = v_n_4627_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4629_; 
v_body_4629_ = lean_ctor_get(v_x_4608_, 3);
v_x_4608_ = v_body_4629_;
goto _start;
}
case 10:
{
lean_object* v_expr_4631_; 
v_expr_4631_ = lean_ctor_get(v_x_4608_, 1);
v_x_4608_ = v_expr_4631_;
goto _start;
}
default: 
{
lean_dec(v_x_4609_);
goto v___jp_4611_;
}
}
v___jp_4611_:
{
uint8_t v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4612_ = 2;
v___x_4613_ = lean_box(v___x_4612_);
v___x_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4613_);
return v___x_4614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4633_, lean_object* v_x_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4633_, v_x_4634_);
lean_dec_ref(v_x_4633_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4637_, lean_object* v_x_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
lean_object* v___x_4644_; 
v___x_4644_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4637_, v_x_4638_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4645_, lean_object* v_x_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4645_, v_x_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec_ref(v_a_4647_);
lean_dec_ref(v_x_4645_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4653_, lean_object* v_x_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
switch(lean_obj_tag(v_x_4653_))
{
case 4:
{
lean_object* v_declName_4660_; lean_object* v_us_4661_; lean_object* v___x_4662_; 
v_declName_4660_ = lean_ctor_get(v_x_4653_, 0);
lean_inc(v_declName_4660_);
v_us_4661_ = lean_ctor_get(v_x_4653_, 1);
lean_inc(v_us_4661_);
lean_dec_ref_known(v_x_4653_, 2);
v___x_4662_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4660_, v_us_4661_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4664_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v___x_4664_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4663_, v_x_4654_);
lean_dec(v_a_4663_);
return v___x_4664_;
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
lean_dec(v_x_4654_);
v_a_4665_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4662_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4662_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4673_; lean_object* v___x_4674_; 
v_fvarId_4673_ = lean_ctor_get(v_x_4653_, 0);
lean_inc(v_fvarId_4673_);
lean_dec_ref_known(v_x_4653_, 1);
v___x_4674_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4673_, v_a_4655_, v_a_4657_, v_a_4658_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4676_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v___x_4676_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4675_, v_x_4654_);
lean_dec(v_a_4675_);
return v___x_4676_;
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec(v_x_4654_);
v_a_4677_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4674_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4674_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4685_; lean_object* v___x_4686_; 
v_mvarId_4685_ = lean_ctor_get(v_x_4653_, 0);
lean_inc(v_mvarId_4685_);
lean_dec_ref_known(v_x_4653_, 1);
v___x_4686_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4685_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4688_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
v___x_4688_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4687_, v_x_4654_);
lean_dec(v_a_4687_);
return v___x_4688_;
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec(v_x_4654_);
v_a_4689_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4686_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4686_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
case 5:
{
lean_object* v_fn_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v_fn_4697_ = lean_ctor_get(v_x_4653_, 0);
lean_inc_ref(v_fn_4697_);
lean_dec_ref_known(v_x_4653_, 2);
v___x_4698_ = lean_unsigned_to_nat(1u);
v___x_4699_ = lean_nat_add(v_x_4654_, v___x_4698_);
lean_dec(v_x_4654_);
v_x_4653_ = v_fn_4697_;
v_x_4654_ = v___x_4699_;
goto _start;
}
case 10:
{
lean_object* v_expr_4701_; 
v_expr_4701_ = lean_ctor_get(v_x_4653_, 1);
lean_inc_ref(v_expr_4701_);
lean_dec_ref_known(v_x_4653_, 2);
v_x_4653_ = v_expr_4701_;
goto _start;
}
case 8:
{
lean_object* v_body_4703_; 
v_body_4703_ = lean_ctor_get(v_x_4653_, 3);
lean_inc_ref(v_body_4703_);
lean_dec_ref_known(v_x_4653_, 4);
v_x_4653_ = v_body_4703_;
goto _start;
}
case 6:
{
lean_object* v_body_4705_; lean_object* v_zero_4706_; uint8_t v_isZero_4707_; 
v_body_4705_ = lean_ctor_get(v_x_4653_, 2);
lean_inc_ref(v_body_4705_);
lean_dec_ref_known(v_x_4653_, 3);
v_zero_4706_ = lean_unsigned_to_nat(0u);
v_isZero_4707_ = lean_nat_dec_eq(v_x_4654_, v_zero_4706_);
if (v_isZero_4707_ == 1)
{
uint8_t v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
lean_dec_ref(v_body_4705_);
lean_dec(v_x_4654_);
v___x_4708_ = 0;
v___x_4709_ = lean_box(v___x_4708_);
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
return v___x_4710_;
}
else
{
lean_object* v_one_4711_; lean_object* v_n_4712_; 
v_one_4711_ = lean_unsigned_to_nat(1u);
v_n_4712_ = lean_nat_sub(v_x_4654_, v_one_4711_);
lean_dec(v_x_4654_);
v_x_4653_ = v_body_4705_;
v_x_4654_ = v_n_4712_;
goto _start;
}
}
default: 
{
uint8_t v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
lean_dec(v_x_4654_);
lean_dec_ref(v_x_4653_);
v___x_4714_ = 2;
v___x_4715_ = lean_box(v___x_4714_);
v___x_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
return v___x_4716_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4717_, lean_object* v_x_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4717_, v_x_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
switch(lean_obj_tag(v_x_4725_))
{
case 1:
{
lean_object* v_fvarId_4731_; lean_object* v___x_4732_; 
v_fvarId_4731_ = lean_ctor_get(v_x_4725_, 0);
lean_inc(v_fvarId_4731_);
lean_dec_ref_known(v_x_4725_, 1);
v___x_4732_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4731_, v_a_4726_, v_a_4728_, v_a_4729_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_object* v_a_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v___x_4732_, 1);
v___x_4734_ = lean_unsigned_to_nat(0u);
v___x_4735_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4733_, v___x_4734_);
lean_dec(v_a_4733_);
return v___x_4735_;
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
v_a_4736_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4732_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4732_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4744_; lean_object* v___x_4745_; 
v_mvarId_4744_ = lean_ctor_get(v_x_4725_, 0);
lean_inc(v_mvarId_4744_);
lean_dec_ref_known(v_x_4725_, 1);
v___x_4745_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4744_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4746_);
lean_dec_ref_known(v___x_4745_, 1);
v___x_4747_ = lean_unsigned_to_nat(0u);
v___x_4748_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4746_, v___x_4747_);
lean_dec(v_a_4746_);
return v___x_4748_;
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
v_a_4749_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4745_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4745_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
case 3:
{
uint8_t v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec_ref_known(v_x_4725_, 1);
v___x_4757_ = 1;
v___x_4758_ = lean_box(v___x_4757_);
v___x_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4758_);
return v___x_4759_;
}
case 4:
{
lean_object* v_declName_4760_; lean_object* v_us_4761_; lean_object* v___x_4762_; 
v_declName_4760_ = lean_ctor_get(v_x_4725_, 0);
lean_inc(v_declName_4760_);
v_us_4761_ = lean_ctor_get(v_x_4725_, 1);
lean_inc(v_us_4761_);
lean_dec_ref_known(v_x_4725_, 2);
v___x_4762_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4760_, v_us_4761_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_object* v_a_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref_known(v___x_4762_, 1);
v___x_4764_ = lean_unsigned_to_nat(0u);
v___x_4765_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4763_, v___x_4764_);
lean_dec(v_a_4763_);
return v___x_4765_;
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
v_a_4766_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4762_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4762_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
case 5:
{
lean_object* v_fn_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v_fn_4774_ = lean_ctor_get(v_x_4725_, 0);
lean_inc_ref(v_fn_4774_);
lean_dec_ref_known(v_x_4725_, 2);
v___x_4775_ = lean_unsigned_to_nat(1u);
v___x_4776_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4774_, v___x_4775_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
return v___x_4776_;
}
case 6:
{
uint8_t v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
lean_dec_ref_known(v_x_4725_, 3);
v___x_4777_ = 0;
v___x_4778_ = lean_box(v___x_4777_);
v___x_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4778_);
return v___x_4779_;
}
case 7:
{
uint8_t v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
lean_dec_ref_known(v_x_4725_, 3);
v___x_4780_ = 1;
v___x_4781_ = lean_box(v___x_4780_);
v___x_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
return v___x_4782_;
}
case 8:
{
lean_object* v_body_4783_; 
v_body_4783_ = lean_ctor_get(v_x_4725_, 3);
lean_inc_ref(v_body_4783_);
lean_dec_ref_known(v_x_4725_, 4);
v_x_4725_ = v_body_4783_;
goto _start;
}
case 9:
{
uint8_t v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
lean_dec_ref_known(v_x_4725_, 1);
v___x_4785_ = 0;
v___x_4786_ = lean_box(v___x_4785_);
v___x_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
return v___x_4787_;
}
case 10:
{
lean_object* v_expr_4788_; 
v_expr_4788_ = lean_ctor_get(v_x_4725_, 1);
lean_inc_ref(v_expr_4788_);
lean_dec_ref_known(v_x_4725_, 2);
v_x_4725_ = v_expr_4788_;
goto _start;
}
default: 
{
uint8_t v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
lean_dec_ref(v_x_4725_);
v___x_4790_ = 2;
v___x_4791_ = lean_box(v___x_4790_);
v___x_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
return v___x_4792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Lean_Meta_isTypeQuick(v_x_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
lean_dec(v_a_4797_);
lean_dec_ref(v_a_4796_);
lean_dec(v_a_4795_);
lean_dec_ref(v_a_4794_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v___x_4806_; 
lean_inc_ref(v_e_4800_);
v___x_4806_ = l_Lean_Meta_isTypeQuick(v_e_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4856_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4856_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4856_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
uint8_t v___x_4811_; 
v___x_4811_ = lean_unbox(v_a_4807_);
lean_dec(v_a_4807_);
switch(v___x_4811_)
{
case 0:
{
uint8_t v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4815_; 
lean_dec_ref(v_e_4800_);
v___x_4812_ = 0;
v___x_4813_ = lean_box(v___x_4812_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4813_);
v___x_4815_ = v___x_4809_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
case 1:
{
uint8_t v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4820_; 
lean_dec_ref(v_e_4800_);
v___x_4817_ = 1;
v___x_4818_ = lean_box(v___x_4817_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4818_);
v___x_4820_ = v___x_4809_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
default: 
{
lean_object* v___x_4822_; 
lean_del_object(v___x_4809_);
lean_inc(v_a_4804_);
lean_inc_ref(v_a_4803_);
lean_inc(v_a_4802_);
lean_inc_ref(v_a_4801_);
v___x_4822_ = lean_infer_type(v_e_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v___x_4824_ = l_Lean_Meta_whnfD(v_a_4823_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4839_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4827_ = v___x_4824_;
v_isShared_4828_ = v_isSharedCheck_4839_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4824_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4839_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
if (lean_obj_tag(v_a_4825_) == 3)
{
uint8_t v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4832_; 
lean_dec_ref_known(v_a_4825_, 1);
v___x_4829_ = 1;
v___x_4830_ = lean_box(v___x_4829_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 0, v___x_4830_);
v___x_4832_ = v___x_4827_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4830_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
else
{
uint8_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4837_; 
lean_dec(v_a_4825_);
v___x_4834_ = 0;
v___x_4835_ = lean_box(v___x_4834_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 0, v___x_4835_);
v___x_4837_ = v___x_4827_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v___x_4835_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
v_a_4840_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4824_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4824_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
v_a_4848_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4822_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4822_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec_ref(v_e_4800_);
v_a_4857_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4806_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4806_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_Lean_Meta_isType(v_e_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_);
lean_dec(v_a_4869_);
lean_dec_ref(v_a_4868_);
lean_dec(v_a_4867_);
lean_dec_ref(v_a_4866_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4872_){
_start:
{
switch(lean_obj_tag(v_x_4872_))
{
case 7:
{
lean_object* v_body_4873_; 
v_body_4873_ = lean_ctor_get(v_x_4872_, 2);
v_x_4872_ = v_body_4873_;
goto _start;
}
case 3:
{
lean_object* v_u_4875_; lean_object* v___x_4876_; 
v_u_4875_ = lean_ctor_get(v_x_4872_, 0);
lean_inc(v_u_4875_);
v___x_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4876_, 0, v_u_4875_);
return v___x_4876_;
}
default: 
{
lean_object* v___x_4877_; 
v___x_4877_ = lean_box(0);
return v___x_4877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4878_);
lean_dec_ref(v_x_4878_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4880_, lean_object* v_body_4881_, lean_object* v_x_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4880_, v_body_4881_, v_x_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4891_, lean_object* v_xs_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v_l_4899_; 
switch(lean_obj_tag(v_type_4891_))
{
case 3:
{
lean_object* v_u_4902_; 
lean_dec_ref(v_xs_4892_);
v_u_4902_ = lean_ctor_get(v_type_4891_, 0);
lean_inc(v_u_4902_);
lean_dec_ref_known(v_type_4891_, 1);
v_l_4899_ = v_u_4902_;
goto v___jp_4898_;
}
case 7:
{
lean_object* v_binderName_4903_; lean_object* v_binderType_4904_; lean_object* v_body_4905_; uint8_t v_binderInfo_4906_; lean_object* v___f_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v_binderName_4903_ = lean_ctor_get(v_type_4891_, 0);
lean_inc(v_binderName_4903_);
v_binderType_4904_ = lean_ctor_get(v_type_4891_, 1);
lean_inc_ref(v_binderType_4904_);
v_body_4905_ = lean_ctor_get(v_type_4891_, 2);
lean_inc_ref(v_body_4905_);
v_binderInfo_4906_ = lean_ctor_get_uint8(v_type_4891_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4891_, 3);
lean_inc_ref(v_xs_4892_);
v___f_4907_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4907_, 0, v_xs_4892_);
lean_closure_set(v___f_4907_, 1, v_body_4905_);
v___x_4908_ = lean_expr_instantiate_rev(v_binderType_4904_, v_xs_4892_);
lean_dec_ref(v_xs_4892_);
lean_dec_ref(v_binderType_4904_);
v___x_4909_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4903_, v_binderInfo_4906_, v___x_4908_, v___f_4907_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
return v___x_4909_;
}
default: 
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = lean_expr_instantiate_rev(v_type_4891_, v_xs_4892_);
lean_dec_ref(v_xs_4892_);
lean_dec_ref(v_type_4891_);
v___x_4911_ = l_Lean_Meta_whnfD(v___x_4910_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4923_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4923_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4923_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
switch(lean_obj_tag(v_a_4912_))
{
case 3:
{
lean_object* v_u_4916_; 
lean_del_object(v___x_4914_);
v_u_4916_ = lean_ctor_get(v_a_4912_, 0);
lean_inc(v_u_4916_);
lean_dec_ref_known(v_a_4912_, 1);
v_l_4899_ = v_u_4916_;
goto v___jp_4898_;
}
case 7:
{
lean_object* v___x_4917_; 
lean_del_object(v___x_4914_);
v___x_4917_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4891_ = v_a_4912_;
v_xs_4892_ = v___x_4917_;
goto _start;
}
default: 
{
lean_object* v___x_4919_; lean_object* v___x_4921_; 
lean_dec(v_a_4912_);
v___x_4919_ = lean_box(0);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v___x_4919_);
v___x_4921_ = v___x_4914_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
v_a_4924_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4911_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4911_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
}
v___jp_4898_:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4900_, 0, v_l_4899_);
v___x_4901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4900_);
return v___x_4901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4932_, lean_object* v_body_4933_, lean_object* v_x_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = lean_array_push(v_xs_4932_, v_x_4934_);
v___x_4941_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4933_, v___x_4940_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4942_, lean_object* v_xs_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4942_, v_xs_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4950_, lean_object* v_cache_4951_, lean_object* v_a_x3f_4952_){
_start:
{
lean_object* v___x_4954_; lean_object* v_mctx_4955_; lean_object* v_zetaDeltaFVarIds_4956_; lean_object* v_postponed_4957_; lean_object* v_diag_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4968_; 
v___x_4954_ = lean_st_ref_take(v_a_4950_);
v_mctx_4955_ = lean_ctor_get(v___x_4954_, 0);
v_zetaDeltaFVarIds_4956_ = lean_ctor_get(v___x_4954_, 2);
v_postponed_4957_ = lean_ctor_get(v___x_4954_, 3);
v_diag_4958_ = lean_ctor_get(v___x_4954_, 4);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4968_ == 0)
{
lean_object* v_unused_4969_; 
v_unused_4969_ = lean_ctor_get(v___x_4954_, 1);
lean_dec(v_unused_4969_);
v___x_4960_ = v___x_4954_;
v_isShared_4961_ = v_isSharedCheck_4968_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_diag_4958_);
lean_inc(v_postponed_4957_);
lean_inc(v_zetaDeltaFVarIds_4956_);
lean_inc(v_mctx_4955_);
lean_dec(v___x_4954_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4968_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4962_; lean_object* v___x_4964_; 
v___x_4962_ = lean_box(0);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 1, v_cache_4951_);
v___x_4964_ = v___x_4960_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_mctx_4955_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v_cache_4951_);
lean_ctor_set(v_reuseFailAlloc_4967_, 2, v_zetaDeltaFVarIds_4956_);
lean_ctor_set(v_reuseFailAlloc_4967_, 3, v_postponed_4957_);
lean_ctor_set(v_reuseFailAlloc_4967_, 4, v_diag_4958_);
v___x_4964_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4965_ = lean_st_ref_put(v_a_4950_, v___x_4964_);
v___x_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4962_);
return v___x_4966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4970_, lean_object* v_cache_4971_, lean_object* v_a_x3f_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4970_, v_cache_4971_, v_a_x3f_4972_);
lean_dec(v_a_x3f_4972_);
lean_dec(v_a_4970_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v___x_4981_; 
v___x_4981_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4975_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v_cache_4984_; lean_object* v___x_4985_; 
v___x_4982_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4983_ = lean_st_ref_get(v_a_4977_);
v_cache_4984_ = lean_ctor_get(v___x_4983_, 1);
lean_inc_ref(v_cache_4984_);
lean_dec(v___x_4983_);
v___x_4985_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4975_, v___x_4982_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5002_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4988_ = v___x_4985_;
v_isShared_4989_ = v_isSharedCheck_5002_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4985_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5002_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
lean_inc(v_a_4986_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set_tag(v___x_4988_, 1);
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4986_);
v___x_4991_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
v___x_4992_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4977_, v_cache_4984_, v___x_4991_);
lean_dec_ref(v___x_4991_);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_4999_ == 0)
{
lean_object* v_unused_5000_; 
v_unused_5000_ = lean_ctor_get(v___x_4992_, 0);
lean_dec(v_unused_5000_);
v___x_4994_ = v___x_4992_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_dec(v___x_4992_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
lean_ctor_set(v___x_4994_, 0, v_a_4986_);
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4986_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
v_a_5003_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_5003_);
lean_dec_ref_known(v___x_4985_, 1);
v___x_5004_ = lean_box(0);
v___x_5005_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4977_, v_cache_4984_, v___x_5004_);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5012_ == 0)
{
lean_object* v_unused_5013_; 
v_unused_5013_ = lean_ctor_get(v___x_5005_, 0);
lean_dec(v_unused_5013_);
v___x_5007_ = v___x_5005_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_dec(v___x_5005_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
lean_ctor_set_tag(v___x_5007_, 1);
lean_ctor_set(v___x_5007_, 0, v_a_5003_);
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5003_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
else
{
lean_object* v___x_5014_; 
lean_dec_ref(v_type_4975_);
v___x_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5014_, 0, v___x_4981_);
return v___x_5014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_);
lean_dec(v_a_5019_);
lean_dec_ref(v_a_5018_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_){
_start:
{
lean_object* v___x_5028_; 
v___x_5028_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5043_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5031_ = v___x_5028_;
v_isShared_5032_ = v_isSharedCheck_5043_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5028_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5043_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
if (lean_obj_tag(v_a_5029_) == 0)
{
uint8_t v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5033_ = 0;
v___x_5034_ = lean_box(v___x_5033_);
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 0, v___x_5034_);
v___x_5036_ = v___x_5031_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
else
{
uint8_t v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5041_; 
lean_dec_ref_known(v_a_5029_, 1);
v___x_5038_ = 1;
v___x_5039_ = lean_box(v___x_5038_);
if (v_isShared_5032_ == 0)
{
lean_ctor_set(v___x_5031_, 0, v___x_5039_);
v___x_5041_ = v___x_5031_;
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
else
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_a_5044_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___x_5028_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5028_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_Lean_Meta_isTypeFormerType(v_type_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
return v_res_5058_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5059_, lean_object* v_x_5060_){
_start:
{
if (lean_obj_tag(v_x_5059_) == 0)
{
if (lean_obj_tag(v_x_5060_) == 0)
{
uint8_t v___x_5061_; 
v___x_5061_ = 1;
return v___x_5061_;
}
else
{
uint8_t v___x_5062_; 
v___x_5062_ = 0;
return v___x_5062_;
}
}
else
{
if (lean_obj_tag(v_x_5060_) == 0)
{
uint8_t v___x_5063_; 
v___x_5063_ = 0;
return v___x_5063_;
}
else
{
lean_object* v_val_5064_; lean_object* v_val_5065_; uint8_t v___x_5066_; 
v_val_5064_ = lean_ctor_get(v_x_5059_, 0);
v_val_5065_ = lean_ctor_get(v_x_5060_, 0);
v___x_5066_ = lean_level_eq(v_val_5064_, v_val_5065_);
return v___x_5066_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5067_, lean_object* v_x_5068_){
_start:
{
uint8_t v_res_5069_; lean_object* v_r_5070_; 
v_res_5069_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5067_, v_x_5068_);
lean_dec(v_x_5068_);
lean_dec(v_x_5067_);
v_r_5070_ = lean_box(v_res_5069_);
return v_r_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v___x_5079_; 
v___x_5079_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5090_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5082_ = v___x_5079_;
v_isShared_5083_ = v_isSharedCheck_5090_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5079_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5090_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5084_; uint8_t v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5088_; 
v___x_5084_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5085_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5080_, v___x_5084_);
lean_dec(v_a_5080_);
v___x_5086_ = lean_box(v___x_5085_);
if (v_isShared_5083_ == 0)
{
lean_ctor_set(v___x_5082_, 0, v___x_5086_);
v___x_5088_ = v___x_5082_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
else
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
v_a_5091_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v___x_5079_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5079_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Meta_isPropFormerType(v_type_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_);
lean_dec(v_a_5103_);
lean_dec_ref(v_a_5102_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v___x_5112_; 
lean_inc(v_a_5110_);
lean_inc_ref(v_a_5109_);
lean_inc(v_a_5108_);
lean_inc_ref(v_a_5107_);
v___x_5112_ = lean_infer_type(v_e_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v_a_5113_; lean_object* v___x_5114_; 
v_a_5113_ = lean_ctor_get(v___x_5112_, 0);
lean_inc(v_a_5113_);
lean_dec_ref_known(v___x_5112_, 1);
v___x_5114_ = l_Lean_Meta_isTypeFormerType(v_a_5113_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
return v___x_5114_;
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
v_a_5115_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5112_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5112_);
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
v_reuseFailAlloc_5121_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v_res_5129_; 
v_res_5129_ = l_Lean_Meta_isTypeFormer(v_e_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5130_, lean_object* v_maxFVars_x3f_5131_, lean_object* v_k_5132_, uint8_t v_cleanupAnnotations_5133_, uint8_t v_whnfType_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v___f_5140_; lean_object* v___x_5141_; 
v___f_5140_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5140_, 0, v_k_5132_);
v___x_5141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5130_, v_maxFVars_x3f_5131_, v___f_5140_, v_cleanupAnnotations_5133_, v_whnfType_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5144_ = v___x_5141_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5141_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
if (v_isShared_5145_ == 0)
{
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_a_5142_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
v_a_5150_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5141_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5141_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5158_, lean_object* v_maxFVars_x3f_5159_, lean_object* v_k_5160_, lean_object* v_cleanupAnnotations_5161_, lean_object* v_whnfType_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5168_; uint8_t v_whnfType_boxed_5169_; lean_object* v_res_5170_; 
v_cleanupAnnotations_boxed_5168_ = lean_unbox(v_cleanupAnnotations_5161_);
v_whnfType_boxed_5169_ = lean_unbox(v_whnfType_5162_);
v_res_5170_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5158_, v_maxFVars_x3f_5159_, v_k_5160_, v_cleanupAnnotations_boxed_5168_, v_whnfType_boxed_5169_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5171_, lean_object* v_type_5172_, lean_object* v_maxFVars_x3f_5173_, lean_object* v_k_5174_, uint8_t v_cleanupAnnotations_5175_, uint8_t v_whnfType_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v___x_5182_; 
v___x_5182_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5172_, v_maxFVars_x3f_5173_, v_k_5174_, v_cleanupAnnotations_5175_, v_whnfType_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
return v___x_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5183_, lean_object* v_type_5184_, lean_object* v_maxFVars_x3f_5185_, lean_object* v_k_5186_, lean_object* v_cleanupAnnotations_5187_, lean_object* v_whnfType_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5194_; uint8_t v_whnfType_boxed_5195_; lean_object* v_res_5196_; 
v_cleanupAnnotations_boxed_5194_ = lean_unbox(v_cleanupAnnotations_5187_);
v_whnfType_boxed_5195_ = lean_unbox(v_whnfType_5188_);
v_res_5196_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5183_, v_type_5184_, v_maxFVars_x3f_5185_, v_k_5186_, v_cleanupAnnotations_boxed_5194_, v_whnfType_boxed_5195_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
return v_res_5196_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5197_, lean_object* v_as_5198_, size_t v_i_5199_, size_t v_stop_5200_){
_start:
{
uint8_t v___x_5201_; 
v___x_5201_ = lean_usize_dec_eq(v_i_5199_, v_stop_5200_);
if (v___x_5201_ == 0)
{
lean_object* v___x_5202_; uint8_t v___x_5203_; 
v___x_5202_ = lean_array_uget_borrowed(v_as_5198_, v_i_5199_);
v___x_5203_ = lean_expr_eqv(v_a_5197_, v___x_5202_);
if (v___x_5203_ == 0)
{
size_t v___x_5204_; size_t v___x_5205_; 
v___x_5204_ = ((size_t)1ULL);
v___x_5205_ = lean_usize_add(v_i_5199_, v___x_5204_);
v_i_5199_ = v___x_5205_;
goto _start;
}
else
{
return v___x_5203_;
}
}
else
{
uint8_t v___x_5207_; 
v___x_5207_ = 0;
return v___x_5207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5208_, lean_object* v_as_5209_, lean_object* v_i_5210_, lean_object* v_stop_5211_){
_start:
{
size_t v_i_boxed_5212_; size_t v_stop_boxed_5213_; uint8_t v_res_5214_; lean_object* v_r_5215_; 
v_i_boxed_5212_ = lean_unbox_usize(v_i_5210_);
lean_dec(v_i_5210_);
v_stop_boxed_5213_ = lean_unbox_usize(v_stop_5211_);
lean_dec(v_stop_5211_);
v_res_5214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5208_, v_as_5209_, v_i_boxed_5212_, v_stop_boxed_5213_);
lean_dec_ref(v_as_5209_);
lean_dec_ref(v_a_5208_);
v_r_5215_ = lean_box(v_res_5214_);
return v_r_5215_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5216_, lean_object* v_a_5217_){
_start:
{
lean_object* v___x_5218_; lean_object* v___x_5219_; uint8_t v___x_5220_; 
v___x_5218_ = lean_unsigned_to_nat(0u);
v___x_5219_ = lean_array_get_size(v_as_5216_);
v___x_5220_ = lean_nat_dec_lt(v___x_5218_, v___x_5219_);
if (v___x_5220_ == 0)
{
return v___x_5220_;
}
else
{
if (v___x_5220_ == 0)
{
return v___x_5220_;
}
else
{
size_t v___x_5221_; size_t v___x_5222_; uint8_t v___x_5223_; 
v___x_5221_ = ((size_t)0ULL);
v___x_5222_ = lean_usize_of_nat(v___x_5219_);
v___x_5223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5217_, v_as_5216_, v___x_5221_, v___x_5222_);
return v___x_5223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5224_, lean_object* v_a_5225_){
_start:
{
uint8_t v_res_5226_; lean_object* v_r_5227_; 
v_res_5226_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5224_, v_a_5225_);
lean_dec_ref(v_a_5225_);
lean_dec_ref(v_as_5224_);
v_r_5227_ = lean_box(v_res_5226_);
return v_r_5227_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5228_, lean_object* v_e_5229_){
_start:
{
uint8_t v___x_5230_; lean_object* v_d_5232_; lean_object* v_b_5233_; 
v___x_5230_ = l_Lean_Expr_hasFVar(v_e_5229_);
if (v___x_5230_ == 0)
{
lean_dec_ref(v_e_5229_);
return v___x_5230_;
}
else
{
switch(lean_obj_tag(v_e_5229_))
{
case 7:
{
lean_object* v_binderType_5236_; lean_object* v_body_5237_; 
v_binderType_5236_ = lean_ctor_get(v_e_5229_, 1);
lean_inc_ref(v_binderType_5236_);
v_body_5237_ = lean_ctor_get(v_e_5229_, 2);
lean_inc_ref(v_body_5237_);
lean_dec_ref_known(v_e_5229_, 3);
v_d_5232_ = v_binderType_5236_;
v_b_5233_ = v_body_5237_;
goto v___jp_5231_;
}
case 6:
{
lean_object* v_binderType_5238_; lean_object* v_body_5239_; 
v_binderType_5238_ = lean_ctor_get(v_e_5229_, 1);
lean_inc_ref(v_binderType_5238_);
v_body_5239_ = lean_ctor_get(v_e_5229_, 2);
lean_inc_ref(v_body_5239_);
lean_dec_ref_known(v_e_5229_, 3);
v_d_5232_ = v_binderType_5238_;
v_b_5233_ = v_body_5239_;
goto v___jp_5231_;
}
case 10:
{
lean_object* v_expr_5240_; 
v_expr_5240_ = lean_ctor_get(v_e_5229_, 1);
lean_inc_ref(v_expr_5240_);
lean_dec_ref_known(v_e_5229_, 2);
v_e_5229_ = v_expr_5240_;
goto _start;
}
case 8:
{
lean_object* v_type_5242_; lean_object* v_value_5243_; lean_object* v_body_5244_; uint8_t v___x_5245_; 
v_type_5242_ = lean_ctor_get(v_e_5229_, 1);
lean_inc_ref(v_type_5242_);
v_value_5243_ = lean_ctor_get(v_e_5229_, 2);
lean_inc_ref(v_value_5243_);
v_body_5244_ = lean_ctor_get(v_e_5229_, 3);
lean_inc_ref(v_body_5244_);
lean_dec_ref_known(v_e_5229_, 4);
v___x_5245_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5228_, v_type_5242_);
if (v___x_5245_ == 0)
{
uint8_t v___x_5246_; 
v___x_5246_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5228_, v_value_5243_);
if (v___x_5246_ == 0)
{
v_e_5229_ = v_body_5244_;
goto _start;
}
else
{
lean_dec_ref(v_body_5244_);
return v___x_5230_;
}
}
else
{
lean_dec_ref(v_body_5244_);
lean_dec_ref(v_value_5243_);
return v___x_5230_;
}
}
case 5:
{
lean_object* v_fn_5248_; lean_object* v_arg_5249_; uint8_t v___x_5250_; 
v_fn_5248_ = lean_ctor_get(v_e_5229_, 0);
lean_inc_ref(v_fn_5248_);
v_arg_5249_ = lean_ctor_get(v_e_5229_, 1);
lean_inc_ref(v_arg_5249_);
lean_dec_ref_known(v_e_5229_, 2);
v___x_5250_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5228_, v_fn_5248_);
if (v___x_5250_ == 0)
{
v_e_5229_ = v_arg_5249_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5249_);
return v___x_5230_;
}
}
case 11:
{
lean_object* v_struct_5252_; 
v_struct_5252_ = lean_ctor_get(v_e_5229_, 2);
lean_inc_ref(v_struct_5252_);
lean_dec_ref_known(v_e_5229_, 3);
v_e_5229_ = v_struct_5252_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5254_; lean_object* v___x_5255_; uint8_t v___x_5256_; 
v_fvarId_5254_ = lean_ctor_get(v_e_5229_, 0);
lean_inc(v_fvarId_5254_);
lean_dec_ref_known(v_e_5229_, 1);
v___x_5255_ = l_Lean_Expr_fvar___override(v_fvarId_5254_);
v___x_5256_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5228_, v___x_5255_);
lean_dec_ref(v___x_5255_);
return v___x_5256_;
}
default: 
{
uint8_t v___x_5257_; 
lean_dec_ref(v_e_5229_);
v___x_5257_ = 0;
return v___x_5257_;
}
}
}
v___jp_5231_:
{
uint8_t v___x_5234_; 
v___x_5234_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5228_, v_d_5232_);
if (v___x_5234_ == 0)
{
v_e_5229_ = v_b_5233_;
goto _start;
}
else
{
lean_dec_ref(v_b_5233_);
return v___x_5230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5258_, lean_object* v_e_5259_){
_start:
{
uint8_t v_res_5260_; lean_object* v_r_5261_; 
v_res_5260_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5258_, v_e_5259_);
lean_dec_ref(v_xs_5258_);
v_r_5261_ = lean_box(v_res_5260_);
return v_r_5261_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5264_ = l_Lean_stringToMessageData(v___x_5263_);
return v___x_5264_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5266_; lean_object* v___x_5267_; 
v___x_5266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5267_ = l_Lean_stringToMessageData(v___x_5266_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5268_, lean_object* v_type_5269_, lean_object* v_as_5270_, size_t v_sz_5271_, size_t v_i_5272_, lean_object* v_b_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v_a_5280_; uint8_t v___x_5284_; 
v___x_5284_ = lean_usize_dec_lt(v_i_5272_, v_sz_5271_);
if (v___x_5284_ == 0)
{
lean_object* v___x_5285_; 
lean_dec_ref(v_type_5269_);
v___x_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5285_, 0, v_b_5273_);
return v___x_5285_;
}
else
{
lean_object* v___x_5286_; lean_object* v_a_5287_; uint8_t v___x_5288_; 
v___x_5286_ = lean_box(0);
v_a_5287_ = lean_array_uget_borrowed(v_as_5270_, v_i_5272_);
lean_inc(v_a_5287_);
v___x_5288_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5268_, v_a_5287_);
if (v___x_5288_ == 0)
{
v_a_5280_ = v___x_5286_;
goto v___jp_5279_;
}
else
{
lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5289_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5287_);
v___x_5290_ = l_Lean_MessageData_ofExpr(v_a_5287_);
v___x_5291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5289_);
lean_ctor_set(v___x_5291_, 1, v___x_5290_);
v___x_5292_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5291_);
lean_ctor_set(v___x_5293_, 1, v___x_5292_);
lean_inc_ref(v_type_5269_);
v___x_5294_ = l_Lean_MessageData_ofExpr(v_type_5269_);
v___x_5295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5293_);
lean_ctor_set(v___x_5295_, 1, v___x_5294_);
v___x_5296_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5295_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_dec_ref_known(v___x_5296_, 1);
v_a_5280_ = v___x_5286_;
goto v___jp_5279_;
}
else
{
lean_dec_ref(v_type_5269_);
return v___x_5296_;
}
}
}
v___jp_5279_:
{
size_t v___x_5281_; size_t v___x_5282_; 
v___x_5281_ = ((size_t)1ULL);
v___x_5282_ = lean_usize_add(v_i_5272_, v___x_5281_);
v_i_5272_ = v___x_5282_;
v_b_5273_ = v_a_5280_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5297_, lean_object* v_type_5298_, lean_object* v_as_5299_, lean_object* v_sz_5300_, lean_object* v_i_5301_, lean_object* v_b_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_){
_start:
{
size_t v_sz_boxed_5308_; size_t v_i_boxed_5309_; lean_object* v_res_5310_; 
v_sz_boxed_5308_ = lean_unbox_usize(v_sz_5300_);
lean_dec(v_sz_5300_);
v_i_boxed_5309_ = lean_unbox_usize(v_i_5301_);
lean_dec(v_i_5301_);
v_res_5310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5297_, v_type_5298_, v_as_5299_, v_sz_boxed_5308_, v_i_boxed_5309_, v_b_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec_ref(v_as_5299_);
lean_dec_ref(v_xs_5297_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5311_, size_t v_i_5312_, lean_object* v_bs_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
uint8_t v___x_5319_; 
v___x_5319_ = lean_usize_dec_lt(v_i_5312_, v_sz_5311_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
v___x_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5320_, 0, v_bs_5313_);
return v___x_5320_;
}
else
{
lean_object* v_v_5321_; lean_object* v___x_5322_; lean_object* v_bs_x27_5323_; lean_object* v___x_5324_; 
v_v_5321_ = lean_array_uget(v_bs_5313_, v_i_5312_);
v___x_5322_ = lean_unsigned_to_nat(0u);
v_bs_x27_5323_ = lean_array_uset(v_bs_5313_, v_i_5312_, v___x_5322_);
lean_inc(v___y_5317_);
lean_inc_ref(v___y_5316_);
lean_inc(v___y_5315_);
lean_inc_ref(v___y_5314_);
v___x_5324_ = lean_infer_type(v_v_5321_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; size_t v___x_5326_; size_t v___x_5327_; lean_object* v___x_5328_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
lean_inc(v_a_5325_);
lean_dec_ref_known(v___x_5324_, 1);
v___x_5326_ = ((size_t)1ULL);
v___x_5327_ = lean_usize_add(v_i_5312_, v___x_5326_);
v___x_5328_ = lean_array_uset(v_bs_x27_5323_, v_i_5312_, v_a_5325_);
v_i_5312_ = v___x_5327_;
v_bs_5313_ = v___x_5328_;
goto _start;
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
lean_dec_ref(v_bs_x27_5323_);
v_a_5330_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5332_ = v___x_5324_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5324_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5338_, lean_object* v_i_5339_, lean_object* v_bs_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_){
_start:
{
size_t v_sz_boxed_5346_; size_t v_i_boxed_5347_; lean_object* v_res_5348_; 
v_sz_boxed_5346_ = lean_unbox_usize(v_sz_5338_);
lean_dec(v_sz_5338_);
v_i_boxed_5347_ = lean_unbox_usize(v_i_5339_);
lean_dec(v_i_5339_);
v_res_5348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5346_, v_i_boxed_5347_, v_bs_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
return v_res_5348_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5350_; lean_object* v___x_5351_; 
v___x_5350_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5351_ = l_Lean_stringToMessageData(v___x_5350_);
return v___x_5351_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5353_; lean_object* v___x_5354_; 
v___x_5353_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5354_ = l_Lean_stringToMessageData(v___x_5353_);
return v___x_5354_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5356_; lean_object* v___x_5357_; 
v___x_5356_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5357_ = l_Lean_stringToMessageData(v___x_5356_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5358_, lean_object* v_n_5359_, lean_object* v_xs_5360_, lean_object* v_x_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v___x_5391_; uint8_t v___x_5392_; 
v___x_5391_ = lean_array_get_size(v_xs_5360_);
v___x_5392_ = lean_nat_dec_eq(v___x_5391_, v_n_5359_);
if (v___x_5392_ == 0)
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v_a_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5412_; 
lean_dec_ref(v_xs_5360_);
v___x_5393_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5394_ = l_Lean_MessageData_ofExpr(v_type_5358_);
v___x_5395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5395_, 0, v___x_5393_);
lean_ctor_set(v___x_5395_, 1, v___x_5394_);
v___x_5396_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5395_);
lean_ctor_set(v___x_5397_, 1, v___x_5396_);
v___x_5398_ = l_Nat_reprFast(v_n_5359_);
v___x_5399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5399_, 0, v___x_5398_);
v___x_5400_ = l_Lean_MessageData_ofFormat(v___x_5399_);
v___x_5401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5397_);
lean_ctor_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5403_, 0, v___x_5401_);
lean_ctor_set(v___x_5403_, 1, v___x_5402_);
v___x_5404_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5403_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
v_a_5405_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5412_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5412_ == 0)
{
v___x_5407_ = v___x_5404_;
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_a_5405_);
lean_dec(v___x_5404_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v___x_5410_; 
if (v_isShared_5408_ == 0)
{
v___x_5410_ = v___x_5407_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5405_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
return v___x_5410_;
}
}
}
else
{
lean_dec(v_n_5359_);
goto v___jp_5367_;
}
v___jp_5367_:
{
size_t v_sz_5368_; size_t v___x_5369_; lean_object* v___x_5370_; 
v_sz_5368_ = lean_array_size(v_xs_5360_);
v___x_5369_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5360_);
v___x_5370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5368_, v___x_5369_, v_xs_5360_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
if (lean_obj_tag(v___x_5370_) == 0)
{
lean_object* v_a_5371_; lean_object* v___x_5372_; size_t v_sz_5373_; lean_object* v___x_5374_; 
v_a_5371_ = lean_ctor_get(v___x_5370_, 0);
lean_inc(v_a_5371_);
lean_dec_ref_known(v___x_5370_, 1);
v___x_5372_ = lean_box(0);
v_sz_5373_ = lean_array_size(v_a_5371_);
v___x_5374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5360_, v_type_5358_, v_a_5371_, v_sz_5373_, v___x_5369_, v___x_5372_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
lean_dec_ref(v_xs_5360_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5381_ == 0)
{
lean_object* v_unused_5382_; 
v_unused_5382_ = lean_ctor_get(v___x_5374_, 0);
lean_dec(v_unused_5382_);
v___x_5376_ = v___x_5374_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_dec(v___x_5374_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v_a_5371_);
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5371_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
lean_dec(v_a_5371_);
v_a_5383_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5374_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5374_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
return v___x_5388_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5360_);
lean_dec_ref(v_type_5358_);
return v___x_5370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5413_, lean_object* v_n_5414_, lean_object* v_xs_5415_, lean_object* v_x_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v_res_5422_; 
v_res_5422_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5413_, v_n_5414_, v_xs_5415_, v_x_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec_ref(v_x_5416_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5423_, lean_object* v_type_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_, lean_object* v_a_5428_){
_start:
{
lean_object* v___f_5430_; lean_object* v___x_5431_; uint8_t v___x_5432_; lean_object* v___x_5433_; 
lean_inc(v_n_5423_);
lean_inc_ref(v_type_5424_);
v___f_5430_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5430_, 0, v_type_5424_);
lean_closure_set(v___f_5430_, 1, v_n_5423_);
v___x_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5431_, 0, v_n_5423_);
v___x_5432_ = 0;
v___x_5433_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5424_, v___x_5431_, v___f_5430_, v___x_5432_, v___x_5432_, v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5434_, lean_object* v_type_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Lean_Meta_arrowDomainsN(v_n_5434_, v_type_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_);
lean_dec(v_a_5439_);
lean_dec_ref(v_a_5438_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5442_, lean_object* v_e_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_){
_start:
{
lean_object* v___x_5449_; 
lean_inc(v_a_5447_);
lean_inc_ref(v_a_5446_);
lean_inc(v_a_5445_);
lean_inc_ref(v_a_5444_);
v___x_5449_ = lean_infer_type(v_e_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5451_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_a_5450_);
lean_dec_ref_known(v___x_5449_, 1);
v___x_5451_ = l_Lean_Meta_arrowDomainsN(v_n_5442_, v_a_5450_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_);
return v___x_5451_;
}
else
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5459_; 
lean_dec(v_n_5442_);
v_a_5452_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5459_ == 0)
{
v___x_5454_ = v___x_5449_;
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v___x_5449_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5457_; 
if (v_isShared_5455_ == 0)
{
v___x_5457_ = v___x_5454_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5452_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5460_, lean_object* v_e_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l_Lean_Meta_inferArgumentTypesN(v_n_5460_, v_e_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
return v_res_5467_;
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
