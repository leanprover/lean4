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
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
lean_ctor_set(v___x_993_, 3, v___x_992_);
lean_ctor_set(v___x_993_, 4, v___x_991_);
lean_ctor_set(v___x_993_, 5, v___x_991_);
lean_ctor_set(v___x_993_, 6, v___x_991_);
lean_ctor_set(v___x_993_, 7, v___x_991_);
lean_ctor_set(v___x_993_, 8, v___x_991_);
lean_ctor_set(v___x_993_, 9, v___x_991_);
lean_ctor_set(v___x_993_, 10, v___x_991_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_unsigned_to_nat(32u);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_997_ = ((size_t)5ULL);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_unsigned_to_nat(32u);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_999_);
v___x_1001_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1002_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
lean_ctor_set(v___x_1002_, 2, v___x_998_);
lean_ctor_set(v___x_1002_, 3, v___x_998_);
lean_ctor_set_usize(v___x_1002_, 4, v___x_997_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = lean_box(1);
v___x_1004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
lean_ctor_set(v___x_1006_, 2, v___x_1003_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1028_, lean_object* v_declHint_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v_env_1034_; uint8_t v___x_1035_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_st_ref_get(v___y_1030_);
v_env_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc_ref(v_env_1034_);
lean_dec(v___x_1033_);
v___x_1035_ = l_Lean_Name_isAnonymous(v_declHint_1029_);
if (v___x_1035_ == 0)
{
uint8_t v_isExporting_1036_; 
v_isExporting_1036_ = lean_ctor_get_uint8(v_env_1034_, sizeof(void*)*13);
if (v_isExporting_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref(v_env_1034_);
lean_dec(v_declHint_1029_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_msg_1028_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
lean_inc_ref(v_env_1034_);
v___x_1038_ = l_Lean_Environment_setExporting(v_env_1034_, v___x_1035_);
lean_inc(v_declHint_1029_);
lean_inc_ref(v___x_1038_);
v___x_1039_ = l_Lean_Environment_contains(v___x_1038_, v_declHint_1029_, v_isExporting_1036_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref(v___x_1038_);
lean_dec_ref(v_env_1034_);
lean_dec(v_declHint_1029_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_msg_1028_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_c_1046_; lean_object* v___x_1047_; 
v___x_1041_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1042_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1043_ = l_Lean_Options_empty;
v___x_1044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1038_);
lean_ctor_set(v___x_1044_, 1, v___x_1041_);
lean_ctor_set(v___x_1044_, 2, v___x_1042_);
lean_ctor_set(v___x_1044_, 3, v___x_1043_);
lean_inc(v_declHint_1029_);
v___x_1045_ = l_Lean_MessageData_ofConstName(v_declHint_1029_, v___x_1035_);
v_c_1046_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1046_, 0, v___x_1044_);
lean_ctor_set(v_c_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1034_, v_declHint_1029_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref(v_env_1034_);
lean_dec(v_declHint_1029_);
v___x_1048_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_c_1046_);
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_MessageData_note(v___x_1051_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_msg_1028_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
else
{
lean_object* v_val_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1089_; 
v_val_1055_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1057_ = v___x_1047_;
v_isShared_1058_ = v_isSharedCheck_1089_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_val_1055_);
lean_dec(v___x_1047_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1089_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_mod_1061_; uint8_t v___x_1062_; 
v___x_1059_ = l_Lean_Environment_header(v_env_1034_);
lean_dec_ref(v_env_1034_);
v___x_1060_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1059_);
v_mod_1061_ = lean_array_get(v___x_1032_, v___x_1060_, v_val_1055_);
lean_dec(v_val_1055_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = l_Lean_isPrivateName(v_declHint_1029_);
lean_dec(v_declHint_1029_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_c_1046_);
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l_Lean_MessageData_ofName(v_mod_1061_);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_MessageData_note(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_msg_1028_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1072_);
v___x_1074_ = v___x_1057_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1076_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_c_1046_);
v___x_1078_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_MessageData_ofName(v_mod_1061_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_MessageData_note(v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_msg_1028_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1085_);
v___x_1087_ = v___x_1057_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1090_; 
lean_dec_ref(v_env_1034_);
lean_dec(v_declHint_1029_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_msg_1028_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1091_, lean_object* v_declHint_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1091_, v_declHint_1092_, v___y_1093_);
lean_dec(v___y_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1113_; 
v___x_1103_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1096_, v_declHint_1097_, v___y_1101_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1113_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = l_Lean_unknownIdentifierMessageTag;
v___x_1109_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_a_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1114_, lean_object* v_declHint_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1114_, v_declHint_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1122_, lean_object* v_msg_1123_, lean_object* v_declHint_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v_a_1131_; lean_object* v___x_1132_; 
v___x_1130_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1123_, v_declHint_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1122_, v_a_1131_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1133_, lean_object* v_msg_1134_, lean_object* v_declHint_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1133_, v_msg_1134_, v_declHint_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v_ref_1133_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1148_, lean_object* v_constName_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1155_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1156_ = 0;
lean_inc(v_constName_1149_);
v___x_1157_ = l_Lean_MessageData_ofConstName(v_constName_1149_, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1148_, v___x_1160_, v_constName_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1162_, lean_object* v_constName_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1162_, v_constName_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v_ref_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_ref_1176_; lean_object* v___x_1177_; 
v_ref_1176_ = lean_ctor_get(v___y_1173_, 2);
v___x_1177_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1176_, v_constName_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v_env_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1191_ = lean_st_ref_get(v___y_1189_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc_ref(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = 0;
lean_inc(v_constName_1185_);
v___x_1194_ = l_Lean_Environment_findConstVal_x3f(v_env_1192_, v_constName_1185_, v___x_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1195_;
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_constName_1185_);
v_val_1196_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1194_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_val_1196_);
lean_dec(v___x_1194_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 0);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_val_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1211_, lean_object* v_us_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; 
lean_inc(v_c_1211_);
v___x_1218_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1211_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v_levelParams_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v_levelParams_1220_ = lean_ctor_get(v_a_1219_, 1);
v___x_1221_ = l_List_lengthTR___redArg(v_levelParams_1220_);
v___x_1222_ = l_List_lengthTR___redArg(v_us_1212_);
v___x_1223_ = lean_nat_dec_eq(v___x_1221_, v___x_1222_);
lean_dec(v___x_1222_);
lean_dec(v___x_1221_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_dec(v_a_1219_);
v___x_1224_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1211_, v_us_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; 
lean_dec(v_c_1211_);
v___x_1225_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1219_, v_us_1212_, v_a_1216_);
return v___x_1225_;
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_us_1212_);
lean_dec(v_c_1211_);
v_a_1226_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1218_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1218_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1234_, lean_object* v_us_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1234_, v_us_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1242_, lean_object* v_constName_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_constName_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1250_, v_constName_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1258_, lean_object* v_ref_1259_, lean_object* v_constName_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1259_, v_constName_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_ref_1268_, lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1267_, v_ref_1268_, v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v_ref_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1276_, lean_object* v_ref_1277_, lean_object* v_msg_1278_, lean_object* v_declHint_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1277_, v_msg_1278_, v_declHint_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_ref_1287_, lean_object* v_msg_1288_, lean_object* v_declHint_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1286_, v_ref_1287_, v_msg_1288_, v_declHint_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v_ref_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1296_, lean_object* v_declHint_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1296_, v_declHint_1297_, v___y_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1304_, lean_object* v_declHint_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1304_, v_declHint_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1312_, lean_object* v_ref_1313_, lean_object* v_msg_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1313_, v_msg_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_ref_1322_, lean_object* v_msg_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1321_, v_ref_1322_, v_msg_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v_ref_1322_);
return v_res_1329_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1336_, lean_object* v_idx_1337_, lean_object* v_e_1338_, lean_object* v_a_1339_, lean_object* v_00_u03b1_1340_, lean_object* v_x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1347_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1348_ = l_Lean_mkProj(v_structName_1336_, v_idx_1337_, v_e_1338_);
v___x_1349_ = l_Lean_indentExpr(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1347_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_indentExpr(v_a_1339_);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1354_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1356_, lean_object* v_idx_1357_, lean_object* v_e_1358_, lean_object* v_a_1359_, lean_object* v_00_u03b1_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1356_, v_idx_1357_, v_e_1358_, v_a_1359_, v_00_u03b1_1360_, v_x_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v_env_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_st_ref_get(v___y_1372_);
v_env_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_env_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = 0;
lean_inc(v_constName_1368_);
v___x_1377_ = l_Lean_Environment_find_x3f(v_env_1375_, v_constName_1368_, v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v___x_1378_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_constName_1368_);
v_val_1379_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1377_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_val_1379_);
lean_dec(v___x_1377_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 0);
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_val_1379_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1394_, lean_object* v_structName_1395_, lean_object* v_e_1396_, lean_object* v_idx_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_b_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_a_1407_; uint8_t v___x_1411_; 
v___x_1411_ = lean_nat_dec_lt(v_a_1399_, v_upperBound_1394_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_idx_1397_);
lean_dec_ref(v_e_1396_);
lean_dec(v_structName_1395_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_b_1400_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; 
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
v___x_1413_ = lean_whnf(v_b_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
if (lean_obj_tag(v_a_1414_) == 7)
{
lean_object* v_body_1415_; uint8_t v___x_1416_; 
v_body_1415_ = lean_ctor_get(v_a_1414_, 2);
lean_inc_ref(v_body_1415_);
lean_dec_ref_known(v_a_1414_, 3);
v___x_1416_ = l_Lean_Expr_hasLooseBVars(v_body_1415_);
if (v___x_1416_ == 0)
{
v_a_1407_ = v_body_1415_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_inc_ref(v_e_1396_);
lean_inc(v_a_1399_);
lean_inc(v_structName_1395_);
v___x_1417_ = l_Lean_mkProj(v_structName_1395_, v_a_1399_, v_e_1396_);
v___x_1418_ = lean_expr_instantiate1(v_body_1415_, v___x_1417_);
lean_dec_ref(v___x_1417_);
lean_dec_ref(v_body_1415_);
v_a_1407_ = v___x_1418_;
goto v___jp_1406_;
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1419_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1396_);
lean_inc(v_idx_1397_);
lean_inc(v_structName_1395_);
v___x_1420_ = l_Lean_mkProj(v_structName_1395_, v_idx_1397_, v_e_1396_);
v___x_1421_ = l_Lean_indentExpr(v___x_1420_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1419_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
lean_inc_ref(v_a_1398_);
v___x_1425_ = l_Lean_indentExpr(v_a_1398_);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1426_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec_ref_known(v___x_1427_, 1);
v_a_1407_ = v_a_1414_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_a_1414_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_idx_1397_);
lean_dec_ref(v_e_1396_);
lean_dec(v_structName_1395_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_idx_1397_);
lean_dec_ref(v_e_1396_);
lean_dec(v_structName_1395_);
return v___x_1413_;
}
}
v___jp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_add(v_a_1399_, v___x_1408_);
lean_dec(v_a_1399_);
v_a_1399_ = v___x_1409_;
v_b_1400_ = v_a_1407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1436_, lean_object* v_structName_1437_, lean_object* v_e_1438_, lean_object* v_idx_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1436_, v_structName_1437_, v_e_1438_, v_idx_1439_, v_a_1440_, v_a_1441_, v_b_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v_upperBound_1436_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1449_, lean_object* v_structName_1450_, lean_object* v_e_1451_, lean_object* v_idx_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_a_1462_; uint8_t v___x_1466_; 
v___x_1466_ = lean_nat_dec_lt(v_a_1454_, v_upperBound_1449_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; 
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_idx_1452_);
lean_dec_ref(v_e_1451_);
lean_dec(v_structName_1450_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_b_1455_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; 
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
v___x_1468_ = lean_whnf(v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
if (lean_obj_tag(v_a_1469_) == 7)
{
lean_object* v_body_1470_; uint8_t v___x_1471_; 
v_body_1470_ = lean_ctor_get(v_a_1469_, 2);
lean_inc_ref(v_body_1470_);
lean_dec_ref_known(v_a_1469_, 3);
v___x_1471_ = l_Lean_Expr_hasLooseBVars(v_body_1470_);
if (v___x_1471_ == 0)
{
v_a_1462_ = v_body_1470_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v_e_1451_);
lean_inc(v_a_1454_);
lean_inc(v_structName_1450_);
v___x_1472_ = l_Lean_mkProj(v_structName_1450_, v_a_1454_, v_e_1451_);
v___x_1473_ = lean_expr_instantiate1(v_body_1470_, v___x_1472_);
lean_dec_ref(v___x_1472_);
lean_dec_ref(v_body_1470_);
v_a_1462_ = v___x_1473_;
goto v___jp_1461_;
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1474_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1451_);
lean_inc(v_idx_1452_);
lean_inc(v_structName_1450_);
v___x_1475_ = l_Lean_mkProj(v_structName_1450_, v_idx_1452_, v_e_1451_);
v___x_1476_ = l_Lean_indentExpr(v___x_1475_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1474_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_inc_ref(v_a_1453_);
v___x_1480_ = l_Lean_indentExpr(v_a_1453_);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1481_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_dec_ref_known(v___x_1482_, 1);
v_a_1462_ = v_a_1469_;
goto v___jp_1461_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_a_1469_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_idx_1452_);
lean_dec_ref(v_e_1451_);
lean_dec(v_structName_1450_);
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
else
{
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_idx_1452_);
lean_dec_ref(v_e_1451_);
lean_dec(v_structName_1450_);
return v___x_1468_;
}
}
v___jp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = lean_nat_add(v_a_1454_, v___x_1463_);
lean_dec(v_a_1454_);
v___x_1465_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1449_, v_structName_1450_, v_e_1451_, v_idx_1452_, v_a_1453_, v___x_1464_, v_a_1462_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1491_, lean_object* v_structName_1492_, lean_object* v_e_1493_, lean_object* v_idx_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1491_, v_structName_1492_, v_e_1493_, v_idx_1494_, v_a_1495_, v_a_1496_, v_b_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v_upperBound_1491_);
return v_res_1503_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1504_; lean_object* v_dummy_1505_; 
v___x_1504_ = lean_box(0);
v_dummy_1505_ = l_Lean_Expr_sort___override(v___x_1504_);
return v_dummy_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1506_, lean_object* v_idx_1507_, lean_object* v_e_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v___x_1514_; 
lean_inc(v_a_1512_);
lean_inc_ref(v_a_1511_);
lean_inc(v_a_1510_);
lean_inc_ref(v_a_1509_);
lean_inc_ref(v_e_1508_);
v___x_1514_ = lean_infer_type(v_e_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
lean_inc(v_a_1512_);
lean_inc_ref(v_a_1511_);
lean_inc(v_a_1510_);
lean_inc_ref(v_a_1509_);
v___x_1516_ = lean_whnf(v_a_1515_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_Expr_getAppFn(v_a_1517_);
if (lean_obj_tag(v___x_1518_) == 4)
{
lean_object* v_declName_1519_; lean_object* v_us_1520_; lean_object* v___x_1521_; lean_object* v_env_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; 
v_declName_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_declName_1519_);
v_us_1520_ = lean_ctor_get(v___x_1518_, 1);
lean_inc(v_us_1520_);
lean_dec_ref_known(v___x_1518_, 2);
v___x_1521_ = lean_st_ref_get(v_a_1512_);
v_env_1525_ = lean_ctor_get(v___x_1521_, 0);
lean_inc_ref(v_env_1525_);
lean_dec(v___x_1521_);
v___x_1526_ = 0;
v___x_1527_ = l_Lean_Environment_find_x3f(v_env_1525_, v_declName_1519_, v___x_1526_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_us_1520_);
v___x_1528_ = lean_box(0);
v___x_1529_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1528_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
return v___x_1529_;
}
else
{
lean_object* v_val_1530_; 
v_val_1530_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_val_1530_);
lean_dec_ref_known(v___x_1527_, 1);
if (lean_obj_tag(v_val_1530_) == 5)
{
lean_object* v_val_1531_; lean_object* v_ctors_1532_; 
v_val_1531_ = lean_ctor_get(v_val_1530_, 0);
lean_inc_ref(v_val_1531_);
lean_dec_ref_known(v_val_1530_, 1);
v_ctors_1532_ = lean_ctor_get(v_val_1531_, 4);
lean_inc(v_ctors_1532_);
if (lean_obj_tag(v_ctors_1532_) == 1)
{
lean_object* v_tail_1533_; 
v_tail_1533_ = lean_ctor_get(v_ctors_1532_, 1);
if (lean_obj_tag(v_tail_1533_) == 0)
{
lean_object* v_toConstantVal_1534_; lean_object* v_numParams_1535_; lean_object* v_numIndices_1536_; lean_object* v_head_1537_; lean_object* v___x_1538_; 
v_toConstantVal_1534_ = lean_ctor_get(v_val_1531_, 0);
lean_inc_ref(v_toConstantVal_1534_);
v_numParams_1535_ = lean_ctor_get(v_val_1531_, 1);
lean_inc(v_numParams_1535_);
v_numIndices_1536_ = lean_ctor_get(v_val_1531_, 2);
lean_inc(v_numIndices_1536_);
lean_dec_ref(v_val_1531_);
v_head_1537_ = lean_ctor_get(v_ctors_1532_, 0);
lean_inc(v_head_1537_);
lean_dec_ref_known(v_ctors_1532_, 2);
v___x_1538_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1537_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
if (lean_obj_tag(v_a_1539_) == 6)
{
lean_object* v_val_1540_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_name_1580_; uint8_t v___x_1581_; 
v_val_1540_ = lean_ctor_get(v_a_1539_, 0);
lean_inc_ref(v_val_1540_);
lean_dec_ref_known(v_a_1539_, 1);
v_name_1580_ = lean_ctor_get(v_toConstantVal_1534_, 0);
lean_inc(v_name_1580_);
lean_dec_ref(v_toConstantVal_1534_);
v___x_1581_ = lean_name_eq(v_name_1580_, v_structName_1506_);
lean_dec(v_name_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_val_1540_);
lean_dec(v_numIndices_1536_);
lean_dec(v_numParams_1535_);
lean_dec(v_us_1520_);
v___x_1582_ = lean_box(0);
v___x_1583_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1582_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
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
else
{
v___y_1542_ = v_a_1509_;
v___y_1543_ = v_a_1510_;
v___y_1544_ = v_a_1511_;
v___y_1545_ = v_a_1512_;
goto v___jp_1541_;
}
v___jp_1541_:
{
lean_object* v_dummy_1546_; lean_object* v_nargs_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_dummy_1546_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1547_ = l_Lean_Expr_getAppNumArgs(v_a_1517_);
lean_inc(v_nargs_1547_);
v___x_1548_ = lean_mk_array(v_nargs_1547_, v_dummy_1546_);
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_sub(v_nargs_1547_, v___x_1549_);
lean_dec(v_nargs_1547_);
lean_inc(v_a_1517_);
v___x_1551_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1517_, v___x_1548_, v___x_1550_);
v___x_1552_ = lean_nat_add(v_numParams_1535_, v_numIndices_1536_);
lean_dec(v_numIndices_1536_);
v___x_1553_ = lean_array_get_size(v___x_1551_);
v___x_1554_ = lean_nat_dec_eq(v___x_1552_, v___x_1553_);
lean_dec(v___x_1552_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref(v___x_1551_);
lean_dec_ref(v_val_1540_);
lean_dec(v_numParams_1535_);
lean_dec(v_us_1520_);
v___x_1555_ = lean_box(0);
v___x_1556_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1555_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1556_;
}
else
{
lean_object* v_toConstantVal_1557_; lean_object* v_name_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_toConstantVal_1557_ = lean_ctor_get(v_val_1540_, 0);
lean_inc_ref(v_toConstantVal_1557_);
lean_dec_ref(v_val_1540_);
v_name_1558_ = lean_ctor_get(v_toConstantVal_1557_, 0);
lean_inc(v_name_1558_);
lean_dec_ref(v_toConstantVal_1557_);
v___x_1559_ = l_Lean_mkConst(v_name_1558_, v_us_1520_);
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = l_Array_toSubarray___redArg(v___x_1551_, v___x_1560_, v_numParams_1535_);
v___x_1562_ = l_Subarray_copy___redArg(v___x_1561_);
v___x_1563_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1559_, v___x_1562_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec_ref(v___x_1562_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
lean_inc(v_a_1517_);
lean_inc_ref(v_e_1508_);
lean_inc(v_structName_1506_);
lean_inc(v_idx_1507_);
v___x_1565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1507_, v_structName_1506_, v_e_1508_, v_idx_1507_, v_a_1517_, v___x_1560_, v_a_1564_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
v___x_1567_ = lean_whnf(v_a_1566_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1579_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
if (lean_obj_tag(v_a_1568_) == 7)
{
lean_object* v_binderType_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec(v_a_1517_);
lean_dec_ref(v_e_1508_);
lean_dec(v_idx_1507_);
lean_dec(v_structName_1506_);
v_binderType_1572_ = lean_ctor_get(v_a_1568_, 1);
lean_inc_ref(v_binderType_1572_);
lean_dec_ref_known(v_a_1568_, 3);
v___x_1573_ = lean_expr_consume_type_annotations(v_binderType_1572_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1573_);
v___x_1575_ = v___x_1570_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_del_object(v___x_1570_);
lean_dec(v_a_1568_);
v___x_1577_ = lean_box(0);
v___x_1578_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1577_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1578_;
}
}
}
else
{
lean_dec(v_a_1517_);
lean_dec_ref(v_e_1508_);
lean_dec(v_idx_1507_);
lean_dec(v_structName_1506_);
return v___x_1567_;
}
}
else
{
lean_dec(v_a_1517_);
lean_dec_ref(v_e_1508_);
lean_dec(v_idx_1507_);
lean_dec(v_structName_1506_);
return v___x_1565_;
}
}
else
{
lean_dec(v_a_1517_);
lean_dec_ref(v_e_1508_);
lean_dec(v_idx_1507_);
lean_dec(v_structName_1506_);
return v___x_1563_;
}
}
}
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec(v_a_1539_);
lean_dec(v_numIndices_1536_);
lean_dec(v_numParams_1535_);
lean_dec_ref(v_toConstantVal_1534_);
lean_dec(v_us_1520_);
v___x_1592_ = lean_box(0);
v___x_1593_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1592_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
return v___x_1593_;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_numIndices_1536_);
lean_dec(v_numParams_1535_);
lean_dec_ref(v_toConstantVal_1534_);
lean_dec(v_us_1520_);
lean_dec(v_a_1517_);
lean_dec_ref(v_e_1508_);
lean_dec(v_idx_1507_);
lean_dec(v_structName_1506_);
v_a_1594_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1538_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1538_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1532_, 2);
lean_dec_ref(v_val_1531_);
lean_dec(v_us_1520_);
goto v___jp_1522_;
}
}
else
{
lean_dec(v_ctors_1532_);
lean_dec_ref(v_val_1531_);
lean_dec(v_us_1520_);
goto v___jp_1522_;
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v_val_1530_);
lean_dec(v_us_1520_);
v___x_1602_ = lean_box(0);
v___x_1603_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1602_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
return v___x_1603_;
}
}
v___jp_1522_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1523_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
return v___x_1524_;
}
}
else
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec_ref(v___x_1518_);
v___x_1604_ = lean_box(0);
v___x_1605_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1506_, v_idx_1507_, v_e_1508_, v_a_1517_, lean_box(0), v___x_1604_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
return v___x_1605_;
}
}
else
{
lean_dec_ref(v_e_1508_);
lean_dec(v_idx_1507_);
lean_dec(v_structName_1506_);
return v___x_1516_;
}
}
else
{
lean_dec_ref(v_e_1508_);
lean_dec(v_idx_1507_);
lean_dec(v_structName_1506_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1606_, lean_object* v_idx_1607_, lean_object* v_e_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1606_, v_idx_1607_, v_e_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1615_, lean_object* v_structName_1616_, lean_object* v_e_1617_, lean_object* v_idx_1618_, lean_object* v_a_1619_, lean_object* v_inst_1620_, lean_object* v_R_1621_, lean_object* v_a_1622_, lean_object* v_b_1623_, lean_object* v_c_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1615_, v_structName_1616_, v_e_1617_, v_idx_1618_, v_a_1619_, v_a_1622_, v_b_1623_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1631_, lean_object* v_structName_1632_, lean_object* v_e_1633_, lean_object* v_idx_1634_, lean_object* v_a_1635_, lean_object* v_inst_1636_, lean_object* v_R_1637_, lean_object* v_a_1638_, lean_object* v_b_1639_, lean_object* v_c_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1631_, v_structName_1632_, v_e_1633_, v_idx_1634_, v_a_1635_, v_inst_1636_, v_R_1637_, v_a_1638_, v_b_1639_, v_c_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v_upperBound_1631_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1647_, lean_object* v_structName_1648_, lean_object* v_e_1649_, lean_object* v_idx_1650_, lean_object* v_a_1651_, lean_object* v_inst_1652_, lean_object* v_R_1653_, lean_object* v_a_1654_, lean_object* v_b_1655_, lean_object* v_c_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1647_, v_structName_1648_, v_e_1649_, v_idx_1650_, v_a_1651_, v_a_1654_, v_b_1655_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1663_, lean_object* v_structName_1664_, lean_object* v_e_1665_, lean_object* v_idx_1666_, lean_object* v_a_1667_, lean_object* v_inst_1668_, lean_object* v_R_1669_, lean_object* v_a_1670_, lean_object* v_b_1671_, lean_object* v_c_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1663_, v_structName_1664_, v_e_1665_, v_idx_1666_, v_a_1667_, v_inst_1668_, v_R_1669_, v_a_1670_, v_b_1671_, v_c_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_upperBound_1663_);
return v_res_1678_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1688_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1689_ = l_Lean_indentExpr(v_type_1682_);
v___x_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1690_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1699_, lean_object* v_type_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_type_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1707_, v_type_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v_ks_1719_; lean_object* v_vs_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1744_; 
v_ks_1719_ = lean_ctor_get(v_x_1715_, 0);
v_vs_1720_ = lean_ctor_get(v_x_1715_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_x_1715_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1722_ = v_x_1715_;
v_isShared_1723_ = v_isSharedCheck_1744_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_vs_1720_);
lean_inc(v_ks_1719_);
lean_dec(v_x_1715_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1744_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1724_ = lean_array_get_size(v_ks_1719_);
v___x_1725_ = lean_nat_dec_lt(v_x_1716_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_dec(v_x_1716_);
v___x_1726_ = lean_array_push(v_ks_1719_, v_x_1717_);
v___x_1727_ = lean_array_push(v_vs_1720_, v_x_1718_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v___x_1727_);
lean_ctor_set(v___x_1722_, 0, v___x_1726_);
v___x_1729_ = v___x_1722_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
else
{
lean_object* v_k_x27_1731_; uint8_t v___x_1732_; 
v_k_x27_1731_ = lean_array_fget_borrowed(v_ks_1719_, v_x_1716_);
v___x_1732_ = l_Lean_instBEqMVarId_beq(v_x_1717_, v_k_x27_1731_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1734_; 
if (v_isShared_1723_ == 0)
{
v___x_1734_ = v___x_1722_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_ks_1719_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_vs_1720_);
v___x_1734_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = lean_unsigned_to_nat(1u);
v___x_1736_ = lean_nat_add(v_x_1716_, v___x_1735_);
lean_dec(v_x_1716_);
v_x_1715_ = v___x_1734_;
v_x_1716_ = v___x_1736_;
goto _start;
}
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1739_ = lean_array_fset(v_ks_1719_, v_x_1716_, v_x_1717_);
v___x_1740_ = lean_array_fset(v_vs_1720_, v_x_1716_, v_x_1718_);
lean_dec(v_x_1716_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v___x_1740_);
lean_ctor_set(v___x_1722_, 0, v___x_1739_);
v___x_1742_ = v___x_1722_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1745_, lean_object* v_k_1746_, lean_object* v_v_1747_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1745_, v___x_1748_, v_k_1746_, v_v_1747_);
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1751_, size_t v_x_1752_, size_t v_x_1753_, lean_object* v_x_1754_, lean_object* v_x_1755_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 0)
{
lean_object* v_es_1756_; size_t v___x_1757_; size_t v___x_1758_; lean_object* v_j_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_es_1756_ = lean_ctor_get(v_x_1751_, 0);
v___x_1757_ = ((size_t)31ULL);
v___x_1758_ = lean_usize_land(v_x_1752_, v___x_1757_);
v_j_1759_ = lean_usize_to_nat(v___x_1758_);
v___x_1760_ = lean_array_get_size(v_es_1756_);
v___x_1761_ = lean_nat_dec_lt(v_j_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_dec(v_j_1759_);
lean_dec(v_x_1755_);
lean_dec(v_x_1754_);
return v_x_1751_;
}
else
{
lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1800_; 
lean_inc_ref(v_es_1756_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_x_1751_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_x_1751_, 0);
lean_dec(v_unused_1801_);
v___x_1763_ = v_x_1751_;
v_isShared_1764_ = v_isSharedCheck_1800_;
goto v_resetjp_1762_;
}
else
{
lean_dec(v_x_1751_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1800_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_v_1765_; lean_object* v___x_1766_; lean_object* v_xs_x27_1767_; lean_object* v___y_1769_; 
v_v_1765_ = lean_array_fget(v_es_1756_, v_j_1759_);
v___x_1766_ = lean_box(0);
v_xs_x27_1767_ = lean_array_fset(v_es_1756_, v_j_1759_, v___x_1766_);
switch(lean_obj_tag(v_v_1765_))
{
case 0:
{
lean_object* v_key_1774_; lean_object* v_val_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1785_; 
v_key_1774_ = lean_ctor_get(v_v_1765_, 0);
v_val_1775_ = lean_ctor_get(v_v_1765_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_v_1765_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1777_ = v_v_1765_;
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_val_1775_);
lean_inc(v_key_1774_);
lean_dec(v_v_1765_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
uint8_t v___x_1779_; 
v___x_1779_ = l_Lean_instBEqMVarId_beq(v_x_1754_, v_key_1774_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_del_object(v___x_1777_);
v___x_1780_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1774_, v_val_1775_, v_x_1754_, v_x_1755_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
v___y_1769_ = v___x_1781_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1783_; 
lean_dec(v_val_1775_);
lean_dec(v_key_1774_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v_x_1755_);
lean_ctor_set(v___x_1777_, 0, v_x_1754_);
v___x_1783_ = v___x_1777_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_x_1754_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_x_1755_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
v___y_1769_ = v___x_1783_;
goto v___jp_1768_;
}
}
}
}
case 1:
{
lean_object* v_node_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1798_; 
v_node_1786_ = lean_ctor_get(v_v_1765_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_v_1765_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1788_ = v_v_1765_;
v_isShared_1789_ = v_isSharedCheck_1798_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_node_1786_);
lean_dec(v_v_1765_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1798_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
size_t v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1790_ = ((size_t)5ULL);
v___x_1791_ = lean_usize_shift_right(v_x_1752_, v___x_1790_);
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_add(v_x_1753_, v___x_1792_);
v___x_1794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1786_, v___x_1791_, v___x_1793_, v_x_1754_, v_x_1755_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1794_);
v___x_1796_ = v___x_1788_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
v___y_1769_ = v___x_1796_;
goto v___jp_1768_;
}
}
}
default: 
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_x_1754_);
lean_ctor_set(v___x_1799_, 1, v_x_1755_);
v___y_1769_ = v___x_1799_;
goto v___jp_1768_;
}
}
v___jp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = lean_array_fset(v_xs_x27_1767_, v_j_1759_, v___y_1769_);
lean_dec(v_j_1759_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1770_);
v___x_1772_ = v___x_1763_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
else
{
lean_object* v_ks_1802_; lean_object* v_vs_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1821_; 
v_ks_1802_ = lean_ctor_get(v_x_1751_, 0);
v_vs_1803_ = lean_ctor_get(v_x_1751_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_x_1751_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1805_ = v_x_1751_;
v_isShared_1806_ = v_isSharedCheck_1821_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_vs_1803_);
lean_inc(v_ks_1802_);
lean_dec(v_x_1751_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1821_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_ks_1802_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_vs_1803_);
v___x_1808_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v_newNode_1809_; size_t v___x_1810_; uint8_t v___x_1811_; 
v_newNode_1809_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1808_, v_x_1754_, v_x_1755_);
v___x_1810_ = ((size_t)7ULL);
v___x_1811_ = lean_usize_dec_le(v___x_1810_, v_x_1753_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1809_);
v___x_1813_ = lean_unsigned_to_nat(4u);
v___x_1814_ = lean_nat_dec_lt(v___x_1812_, v___x_1813_);
lean_dec(v___x_1812_);
if (v___x_1814_ == 0)
{
lean_object* v_ks_1815_; lean_object* v_vs_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_ks_1815_ = lean_ctor_get(v_newNode_1809_, 0);
lean_inc_ref(v_ks_1815_);
v_vs_1816_ = lean_ctor_get(v_newNode_1809_, 1);
lean_inc_ref(v_vs_1816_);
lean_dec_ref(v_newNode_1809_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1819_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1753_, v_ks_1815_, v_vs_1816_, v___x_1817_, v___x_1818_);
lean_dec_ref(v_vs_1816_);
lean_dec_ref(v_ks_1815_);
return v___x_1819_;
}
else
{
return v_newNode_1809_;
}
}
else
{
return v_newNode_1809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1822_, lean_object* v_keys_1823_, lean_object* v_vals_1824_, lean_object* v_i_1825_, lean_object* v_entries_1826_){
_start:
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = lean_array_get_size(v_keys_1823_);
v___x_1828_ = lean_nat_dec_lt(v_i_1825_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_dec(v_i_1825_);
return v_entries_1826_;
}
else
{
lean_object* v_k_1829_; lean_object* v_v_1830_; uint64_t v___x_1831_; size_t v_h_1832_; size_t v___x_1833_; lean_object* v___x_1834_; size_t v___x_1835_; size_t v___x_1836_; size_t v___x_1837_; size_t v_h_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_k_1829_ = lean_array_fget_borrowed(v_keys_1823_, v_i_1825_);
v_v_1830_ = lean_array_fget_borrowed(v_vals_1824_, v_i_1825_);
v___x_1831_ = l_Lean_instHashableMVarId_hash(v_k_1829_);
v_h_1832_ = lean_uint64_to_usize(v___x_1831_);
v___x_1833_ = ((size_t)5ULL);
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_sub(v_depth_1822_, v___x_1835_);
v___x_1837_ = lean_usize_mul(v___x_1833_, v___x_1836_);
v_h_1838_ = lean_usize_shift_right(v_h_1832_, v___x_1837_);
v___x_1839_ = lean_nat_add(v_i_1825_, v___x_1834_);
lean_dec(v_i_1825_);
lean_inc(v_v_1830_);
lean_inc(v_k_1829_);
v___x_1840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1826_, v_h_1838_, v_depth_1822_, v_k_1829_, v_v_1830_);
v_i_1825_ = v___x_1839_;
v_entries_1826_ = v___x_1840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1842_, lean_object* v_keys_1843_, lean_object* v_vals_1844_, lean_object* v_i_1845_, lean_object* v_entries_1846_){
_start:
{
size_t v_depth_boxed_1847_; lean_object* v_res_1848_; 
v_depth_boxed_1847_ = lean_unbox_usize(v_depth_1842_);
lean_dec(v_depth_1842_);
v_res_1848_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1847_, v_keys_1843_, v_vals_1844_, v_i_1845_, v_entries_1846_);
lean_dec_ref(v_vals_1844_);
lean_dec_ref(v_keys_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_){
_start:
{
size_t v_x_1151__boxed_1854_; size_t v_x_1152__boxed_1855_; lean_object* v_res_1856_; 
v_x_1151__boxed_1854_ = lean_unbox_usize(v_x_1850_);
lean_dec(v_x_1850_);
v_x_1152__boxed_1855_ = lean_unbox_usize(v_x_1851_);
lean_dec(v_x_1851_);
v_res_1856_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1849_, v_x_1151__boxed_1854_, v_x_1152__boxed_1855_, v_x_1852_, v_x_1853_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_){
_start:
{
uint64_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1860_ = l_Lean_instHashableMVarId_hash(v_x_1858_);
v___x_1861_ = lean_uint64_to_usize(v___x_1860_);
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1857_, v___x_1861_, v___x_1862_, v_x_1858_, v_x_1859_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1864_, lean_object* v_val_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v_mctx_1869_; lean_object* v_cache_1870_; lean_object* v_zetaDeltaFVarIds_1871_; lean_object* v_postponed_1872_; lean_object* v_diag_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1902_; 
v___x_1868_ = lean_st_ref_take(v___y_1866_);
v_mctx_1869_ = lean_ctor_get(v___x_1868_, 0);
v_cache_1870_ = lean_ctor_get(v___x_1868_, 1);
v_zetaDeltaFVarIds_1871_ = lean_ctor_get(v___x_1868_, 2);
v_postponed_1872_ = lean_ctor_get(v___x_1868_, 3);
v_diag_1873_ = lean_ctor_get(v___x_1868_, 4);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1875_ = v___x_1868_;
v_isShared_1876_ = v_isSharedCheck_1902_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_diag_1873_);
lean_inc(v_postponed_1872_);
lean_inc(v_zetaDeltaFVarIds_1871_);
lean_inc(v_cache_1870_);
lean_inc(v_mctx_1869_);
lean_dec(v___x_1868_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1902_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_depth_1877_; lean_object* v_levelAssignDepth_1878_; lean_object* v_lmvarCounter_1879_; lean_object* v_mvarCounter_1880_; lean_object* v_lDecls_1881_; lean_object* v_decls_1882_; lean_object* v_userNames_1883_; lean_object* v_lAssignment_1884_; lean_object* v_eAssignment_1885_; lean_object* v_dAssignment_1886_; lean_object* v_instanceTypedMVars_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1901_; 
v_depth_1877_ = lean_ctor_get(v_mctx_1869_, 0);
v_levelAssignDepth_1878_ = lean_ctor_get(v_mctx_1869_, 1);
v_lmvarCounter_1879_ = lean_ctor_get(v_mctx_1869_, 2);
v_mvarCounter_1880_ = lean_ctor_get(v_mctx_1869_, 3);
v_lDecls_1881_ = lean_ctor_get(v_mctx_1869_, 4);
v_decls_1882_ = lean_ctor_get(v_mctx_1869_, 5);
v_userNames_1883_ = lean_ctor_get(v_mctx_1869_, 6);
v_lAssignment_1884_ = lean_ctor_get(v_mctx_1869_, 7);
v_eAssignment_1885_ = lean_ctor_get(v_mctx_1869_, 8);
v_dAssignment_1886_ = lean_ctor_get(v_mctx_1869_, 9);
v_instanceTypedMVars_1887_ = lean_ctor_get(v_mctx_1869_, 10);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_mctx_1869_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1889_ = v_mctx_1869_;
v_isShared_1890_ = v_isSharedCheck_1901_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_instanceTypedMVars_1887_);
lean_inc(v_dAssignment_1886_);
lean_inc(v_eAssignment_1885_);
lean_inc(v_lAssignment_1884_);
lean_inc(v_userNames_1883_);
lean_inc(v_decls_1882_);
lean_inc(v_lDecls_1881_);
lean_inc(v_mvarCounter_1880_);
lean_inc(v_lmvarCounter_1879_);
lean_inc(v_levelAssignDepth_1878_);
lean_inc(v_depth_1877_);
lean_dec(v_mctx_1869_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1901_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1891_ = lean_box(0);
v___x_1892_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1885_, v_mvarId_1864_, v_val_1865_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 8, v___x_1892_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_depth_1877_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_levelAssignDepth_1878_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v_lmvarCounter_1879_);
lean_ctor_set(v_reuseFailAlloc_1900_, 3, v_mvarCounter_1880_);
lean_ctor_set(v_reuseFailAlloc_1900_, 4, v_lDecls_1881_);
lean_ctor_set(v_reuseFailAlloc_1900_, 5, v_decls_1882_);
lean_ctor_set(v_reuseFailAlloc_1900_, 6, v_userNames_1883_);
lean_ctor_set(v_reuseFailAlloc_1900_, 7, v_lAssignment_1884_);
lean_ctor_set(v_reuseFailAlloc_1900_, 8, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1900_, 9, v_dAssignment_1886_);
lean_ctor_set(v_reuseFailAlloc_1900_, 10, v_instanceTypedMVars_1887_);
v___x_1894_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1896_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1894_);
v___x_1896_ = v___x_1875_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_zetaDeltaFVarIds_1871_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_postponed_1872_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v_diag_1873_);
v___x_1896_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_st_ref_put(v___y_1866_, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1891_);
return v___x_1898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1903_, lean_object* v_val_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1903_, v_val_1904_, v___y_1905_);
lean_dec(v___y_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1914_; 
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
lean_inc_ref(v_type_1908_);
v___x_1914_ = lean_infer_type(v_type_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1916_ = l_Lean_Meta_whnfD(v_a_1915_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1951_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1951_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1951_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
switch(lean_obj_tag(v_a_1917_))
{
case 3:
{
lean_object* v_u_1921_; lean_object* v___x_1923_; 
lean_dec_ref(v_type_1908_);
v_u_1921_ = lean_ctor_get(v_a_1917_, 0);
lean_inc(v_u_1921_);
lean_dec_ref_known(v_a_1917_, 1);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v_u_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_u_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
case 2:
{
lean_object* v_mvarId_1925_; lean_object* v___x_1926_; 
lean_del_object(v___x_1919_);
v_mvarId_1925_ = lean_ctor_get(v_a_1917_, 0);
lean_inc_n(v_mvarId_1925_, 2);
lean_dec_ref_known(v_a_1917_, 1);
v___x_1926_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1925_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; uint8_t v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = lean_unbox(v_a_1927_);
lean_dec(v_a_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec_ref(v_type_1908_);
v___x_1929_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_n(v_a_1930_, 2);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = l_Lean_mkSort(v_a_1930_);
v___x_1932_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1925_, v___x_1931_, v_a_1910_);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1932_, 0);
lean_dec(v_unused_1940_);
v___x_1934_ = v___x_1932_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_dec(v___x_1932_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_a_1930_);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1930_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_dec(v_mvarId_1925_);
return v___x_1929_;
}
}
else
{
lean_object* v___x_1941_; 
lean_dec(v_mvarId_1925_);
v___x_1941_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1941_;
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_mvarId_1925_);
lean_dec_ref(v_type_1908_);
v_a_1942_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1926_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1926_);
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
default: 
{
lean_object* v___x_1950_; 
lean_del_object(v___x_1919_);
lean_dec(v_a_1917_);
v___x_1950_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_type_1908_);
v_a_1952_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1916_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1916_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v_type_1908_);
v_a_1960_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1914_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1914_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Meta_getLevel(v_type_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1975_, lean_object* v_val_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1975_, v_val_1976_, v___y_1978_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1983_, lean_object* v_val_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1983_, v_val_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1992_, v_x_1993_, v_x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1996_, lean_object* v_x_1997_, size_t v_x_1998_, size_t v_x_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1997_, v_x_1998_, v_x_1999_, v_x_2000_, v_x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2003_, lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
size_t v_x_1500__boxed_2009_; size_t v_x_1501__boxed_2010_; lean_object* v_res_2011_; 
v_x_1500__boxed_2009_ = lean_unbox_usize(v_x_2005_);
lean_dec(v_x_2005_);
v_x_1501__boxed_2010_ = lean_unbox_usize(v_x_2006_);
lean_dec(v_x_2006_);
v_res_2011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2003_, v_x_2004_, v_x_1500__boxed_2009_, v_x_1501__boxed_2010_, v_x_2007_, v_x_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2012_, lean_object* v_n_2013_, lean_object* v_k_2014_, lean_object* v_v_2015_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2013_, v_k_2014_, v_v_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2017_, size_t v_depth_2018_, lean_object* v_keys_2019_, lean_object* v_vals_2020_, lean_object* v_heq_2021_, lean_object* v_i_2022_, lean_object* v_entries_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2018_, v_keys_2019_, v_vals_2020_, v_i_2022_, v_entries_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2025_, lean_object* v_depth_2026_, lean_object* v_keys_2027_, lean_object* v_vals_2028_, lean_object* v_heq_2029_, lean_object* v_i_2030_, lean_object* v_entries_2031_){
_start:
{
size_t v_depth_boxed_2032_; lean_object* v_res_2033_; 
v_depth_boxed_2032_ = lean_unbox_usize(v_depth_2026_);
lean_dec(v_depth_2026_);
v_res_2033_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2025_, v_depth_boxed_2032_, v_keys_2027_, v_vals_2028_, v_heq_2029_, v_i_2030_, v_entries_2031_);
lean_dec_ref(v_vals_2028_);
lean_dec_ref(v_keys_2027_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2035_, v_x_2036_, v_x_2037_, v_x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2040_, lean_object* v_b_2041_, lean_object* v_c_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; 
lean_inc(v___y_2046_);
lean_inc_ref(v___y_2045_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
v___x_2048_ = lean_apply_7(v_k_2040_, v_b_2041_, v_c_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, lean_box(0));
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2049_, lean_object* v_b_2050_, lean_object* v_c_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2049_, v_b_2050_, v_c_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2058_, lean_object* v_k_2059_, uint8_t v_cleanupAnnotations_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___f_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2066_, 0, v_k_2059_);
v___x_2067_ = 0;
v___x_2068_ = lean_box(0);
v___x_2069_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2067_, v___x_2068_, v_type_2058_, v___f_2066_, v_cleanupAnnotations_2060_, v___x_2067_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_a_2078_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2069_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2069_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2086_, lean_object* v_k_2087_, lean_object* v_cleanupAnnotations_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2094_; lean_object* v_res_2095_; 
v_cleanupAnnotations_boxed_2094_ = lean_unbox(v_cleanupAnnotations_2088_);
v_res_2095_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2086_, v_k_2087_, v_cleanupAnnotations_boxed_2094_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2096_, lean_object* v_type_2097_, lean_object* v_k_2098_, uint8_t v_cleanupAnnotations_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2097_, v_k_2098_, v_cleanupAnnotations_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_type_2107_, lean_object* v_k_2108_, lean_object* v_cleanupAnnotations_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2115_; lean_object* v_res_2116_; 
v_cleanupAnnotations_boxed_2115_ = lean_unbox(v_cleanupAnnotations_2109_);
v_res_2116_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2106_, v_type_2107_, v_k_2108_, v_cleanupAnnotations_boxed_2115_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2117_, size_t v_i_2118_, size_t v_stop_2119_, lean_object* v_b_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_usize_dec_eq(v_i_2118_, v_stop_2119_);
if (v___x_2126_ == 0)
{
size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2127_ = ((size_t)1ULL);
v___x_2128_ = lean_usize_sub(v_i_2118_, v___x_2127_);
v___x_2129_ = lean_array_uget_borrowed(v_as_2117_, v___x_2128_);
lean_inc(v___y_2124_);
lean_inc_ref(v___y_2123_);
lean_inc(v___y_2122_);
lean_inc_ref(v___y_2121_);
lean_inc(v___x_2129_);
v___x_2130_ = lean_infer_type(v___x_2129_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l_Lean_Meta_getLevel(v_a_2131_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l_Lean_mkLevelIMax_x27(v_a_2133_, v_b_2120_);
v_i_2118_ = v___x_2128_;
v_b_2120_ = v___x_2134_;
goto _start;
}
else
{
lean_dec(v_b_2120_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2136_; 
v_a_2136_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2132_, 1);
v_i_2118_ = v___x_2128_;
v_b_2120_ = v_a_2136_;
goto _start;
}
else
{
return v___x_2132_;
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_b_2120_);
v_a_2138_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2130_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2130_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_b_2120_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2147_, lean_object* v_i_2148_, lean_object* v_stop_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
size_t v_i_boxed_2156_; size_t v_stop_boxed_2157_; lean_object* v_res_2158_; 
v_i_boxed_2156_ = lean_unbox_usize(v_i_2148_);
lean_dec(v_i_2148_);
v_stop_boxed_2157_ = lean_unbox_usize(v_stop_2149_);
lean_dec(v_stop_2149_);
v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2147_, v_i_boxed_2156_, v_stop_boxed_2157_, v_b_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec_ref(v_as_2147_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2159_, lean_object* v_e_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___y_2167_; lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_Meta_getLevel(v_e_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v___x_2188_ = lean_array_get_size(v_xs_2159_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_nat_dec_lt(v___x_2189_, v___x_2188_);
if (v___x_2190_ == 0)
{
v___y_2167_ = v___x_2186_;
goto v___jp_2166_;
}
else
{
size_t v___x_2191_; size_t v___x_2192_; lean_object* v___x_2193_; 
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v___x_2191_ = lean_usize_of_nat(v___x_2188_);
v___x_2192_ = ((size_t)0ULL);
v___x_2193_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2159_, v___x_2191_, v___x_2192_, v_a_2187_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
v___y_2167_ = v___x_2193_;
goto v___jp_2166_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_a_2194_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2186_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2186_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
v___jp_2166_:
{
if (lean_obj_tag(v___y_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2177_; 
v_a_2168_ = lean_ctor_get(v___y_2167_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___y_2167_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2170_ = v___y_2167_;
v_isShared_2171_ = v_isSharedCheck_2177_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___y_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2177_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2172_ = l_Lean_Level_normalize(v_a_2168_);
lean_dec(v_a_2168_);
v___x_2173_ = l_Lean_mkSort(v___x_2172_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2173_);
v___x_2175_ = v___x_2170_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_a_2178_ = lean_ctor_get(v___y_2167_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___y_2167_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___y_2167_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___y_2167_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2202_, lean_object* v_e_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2202_, v_e_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_xs_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___f_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; 
v___f_2217_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2218_ = 0;
v___x_2219_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2211_, v___f_2217_, v___x_2218_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2227_, lean_object* v_k_2228_, uint8_t v_cleanupAnnotations_2229_, uint8_t v_preserveNondepLet_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___f_2236_; uint8_t v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___f_2236_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2236_, 0, v_k_2228_);
v___x_2237_ = 1;
v___x_2238_ = 0;
v___x_2239_ = lean_box(0);
v___x_2240_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2227_, v___x_2237_, v___x_2237_, v_preserveNondepLet_2230_, v___x_2238_, v___x_2239_, v___f_2236_, v_cleanupAnnotations_2229_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_a_2249_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2240_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2240_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2257_, lean_object* v_k_2258_, lean_object* v_cleanupAnnotations_2259_, lean_object* v_preserveNondepLet_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2266_; uint8_t v_preserveNondepLet_boxed_2267_; lean_object* v_res_2268_; 
v_cleanupAnnotations_boxed_2266_ = lean_unbox(v_cleanupAnnotations_2259_);
v_preserveNondepLet_boxed_2267_ = lean_unbox(v_preserveNondepLet_2260_);
v_res_2268_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2257_, v_k_2258_, v_cleanupAnnotations_boxed_2266_, v_preserveNondepLet_boxed_2267_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2269_, lean_object* v_e_2270_, lean_object* v_k_2271_, uint8_t v_cleanupAnnotations_2272_, uint8_t v_preserveNondepLet_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2270_, v_k_2271_, v_cleanupAnnotations_2272_, v_preserveNondepLet_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_e_2281_, lean_object* v_k_2282_, lean_object* v_cleanupAnnotations_2283_, lean_object* v_preserveNondepLet_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2290_; uint8_t v_preserveNondepLet_boxed_2291_; lean_object* v_res_2292_; 
v_cleanupAnnotations_boxed_2290_ = lean_unbox(v_cleanupAnnotations_2283_);
v_preserveNondepLet_boxed_2291_ = lean_unbox(v_preserveNondepLet_2284_);
v_res_2292_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2280_, v_e_2281_, v_k_2282_, v_cleanupAnnotations_boxed_2290_, v_preserveNondepLet_boxed_2291_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2293_, lean_object* v_e_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
v___x_2300_ = lean_infer_type(v_e_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; uint8_t v___x_2302_; uint8_t v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = 0;
v___x_2303_ = 1;
v___x_2304_ = 1;
v___x_2305_ = l_Lean_Meta_mkForallFVars(v_xs_2293_, v_a_2301_, v___x_2302_, v___x_2303_, v___x_2302_, v___x_2304_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2305_;
}
else
{
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2306_, lean_object* v_e_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2306_, v_e_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v_xs_2306_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___f_2321_; uint8_t v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; 
v___f_2321_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2322_ = 0;
v___x_2323_ = 1;
v___x_2324_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2315_, v___f_2321_, v___x_2322_, v___x_2323_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
return v_res_2331_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2344_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2345_ = l_Lean_MessageData_ofName(v_mvarId_2338_);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2348_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2357_, lean_object* v_mvarId_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2365_, lean_object* v_mvarId_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2365_, v_mvarId_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v_mctx_2380_; lean_object* v___x_2381_; 
v___x_2379_ = lean_st_ref_get(v_a_2375_);
v_mctx_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc_ref(v_mctx_2380_);
lean_dec(v___x_2379_);
v___x_2381_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2380_, v_mvarId_2373_);
lean_dec_ref(v_mctx_2380_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
return v___x_2382_;
}
else
{
lean_object* v_val_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_mvarId_2373_);
v_val_2383_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2385_ = v___x_2381_;
v_isShared_2386_ = v_isSharedCheck_2391_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_val_2383_);
lean_dec(v___x_2381_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2391_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v_type_2387_; lean_object* v___x_2389_; 
v_type_2387_ = lean_ctor_get(v_val_2383_, 2);
lean_inc_ref(v_type_2387_);
lean_dec(v_val_2383_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 0);
lean_ctor_set(v___x_2385_, 0, v_type_2387_);
v___x_2389_ = v___x_2385_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_type_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_lctx_2404_; lean_object* v___x_2405_; 
v_lctx_2404_ = lean_ctor_get(v_a_2400_, 2);
lean_inc(v_fvarId_2399_);
lean_inc_ref(v_lctx_2404_);
v___x_2405_ = lean_local_ctx_find(v_lctx_2404_, v_fvarId_2399_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2399_, v_a_2401_, v_a_2402_);
return v___x_2406_;
}
else
{
lean_object* v_val_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_fvarId_2399_);
v_val_2407_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2409_ = v___x_2405_;
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_val_2407_);
lean_dec(v___x_2405_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2415_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = l_Lean_LocalDecl_type(v_val_2407_);
lean_dec(v_val_2407_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set_tag(v___x_2409_, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2422_, v_a_2423_, v_a_2425_, v_a_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2435_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_instMonadEIO___redArg();
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2438_ = l_StateRefT_x27_instMonad___redArg(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_instMonadExceptOfEIO___redArg();
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___f_2443_; 
v___x_2442_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2443_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2443_, 0, v___x_2442_);
return v___f_2443_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___f_2445_; 
v___x_2444_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2445_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2445_, 0, v___x_2444_);
return v___f_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; 
v___f_2446_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2447_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___f_2447_);
lean_ctor_set(v___x_2448_, 1, v___f_2446_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___f_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2450_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2450_, 0, v___x_2449_);
return v___f_2450_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___f_2452_; 
v___x_2451_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2452_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2452_, 0, v___x_2451_);
return v___f_2452_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; 
v___f_2453_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2454_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___f_2454_);
lean_ctor_set(v___x_2455_, 1, v___f_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2458_, lean_object* v_inferType_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
uint8_t v_cacheInferType_2504_; 
v_cacheInferType_2504_ = lean_ctor_get_uint8(v_a_2460_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2504_ == 0)
{
lean_dec_ref(v_e_2458_);
goto v___jp_2465_;
}
else
{
uint8_t v___x_2505_; 
v___x_2505_ = l_Lean_Expr_hasMVar(v_e_2458_);
if (v___x_2505_ == 0)
{
lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___f_2506_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2507_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
v___x_2508_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2458_, v_a_2460_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2606_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2606_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2606_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2553_; lean_object* v_cache_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2601_; 
v___x_2553_ = lean_st_ref_get(v_a_2461_);
v_cache_2554_ = lean_ctor_get(v___x_2553_, 1);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; lean_object* v_unused_2603_; lean_object* v_unused_2604_; lean_object* v_unused_2605_; 
v_unused_2602_ = lean_ctor_get(v___x_2553_, 4);
lean_dec(v_unused_2602_);
v_unused_2603_ = lean_ctor_get(v___x_2553_, 3);
lean_dec(v_unused_2603_);
v_unused_2604_ = lean_ctor_get(v___x_2553_, 2);
lean_dec(v_unused_2604_);
v_unused_2605_ = lean_ctor_get(v___x_2553_, 0);
lean_dec(v_unused_2605_);
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2601_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_cache_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2601_;
goto v_resetjp_2555_;
}
v___jp_2513_:
{
lean_object* v___x_2514_; 
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
v___x_2514_ = lean_apply_5(v_inferType_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, lean_box(0));
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; uint8_t v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
v___x_2516_ = l_Lean_Expr_hasMVar(v_a_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2551_; 
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; 
v_unused_2552_ = lean_ctor_get(v___x_2514_, 0);
lean_dec(v_unused_2552_);
v___x_2518_ = v___x_2514_;
v_isShared_2519_ = v_isSharedCheck_2551_;
goto v_resetjp_2517_;
}
else
{
lean_dec(v___x_2514_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2551_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v_cache_2521_; lean_object* v_mctx_2522_; lean_object* v_zetaDeltaFVarIds_2523_; lean_object* v_postponed_2524_; lean_object* v_diag_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2550_; 
v___x_2520_ = lean_st_ref_take(v_a_2461_);
v_cache_2521_ = lean_ctor_get(v___x_2520_, 1);
v_mctx_2522_ = lean_ctor_get(v___x_2520_, 0);
v_zetaDeltaFVarIds_2523_ = lean_ctor_get(v___x_2520_, 2);
v_postponed_2524_ = lean_ctor_get(v___x_2520_, 3);
v_diag_2525_ = lean_ctor_get(v___x_2520_, 4);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2527_ = v___x_2520_;
v_isShared_2528_ = v_isSharedCheck_2550_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_diag_2525_);
lean_inc(v_postponed_2524_);
lean_inc(v_zetaDeltaFVarIds_2523_);
lean_inc(v_cache_2521_);
lean_inc(v_mctx_2522_);
lean_dec(v___x_2520_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2550_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_inferType_2529_; lean_object* v_funInfo_2530_; lean_object* v_synthInstance_2531_; lean_object* v_whnf_2532_; lean_object* v_defEqTrans_2533_; lean_object* v_defEqPerm_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2549_; 
v_inferType_2529_ = lean_ctor_get(v_cache_2521_, 0);
v_funInfo_2530_ = lean_ctor_get(v_cache_2521_, 1);
v_synthInstance_2531_ = lean_ctor_get(v_cache_2521_, 2);
v_whnf_2532_ = lean_ctor_get(v_cache_2521_, 3);
v_defEqTrans_2533_ = lean_ctor_get(v_cache_2521_, 4);
v_defEqPerm_2534_ = lean_ctor_get(v_cache_2521_, 5);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_cache_2521_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2536_ = v_cache_2521_;
v_isShared_2537_ = v_isSharedCheck_2549_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_defEqPerm_2534_);
lean_inc(v_defEqTrans_2533_);
lean_inc(v_whnf_2532_);
lean_inc(v_synthInstance_2531_);
lean_inc(v_funInfo_2530_);
lean_inc(v_inferType_2529_);
lean_dec(v_cache_2521_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2549_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_inc(v_a_2515_);
v___x_2538_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2506_, v___x_2507_, v_inferType_2529_, v_a_2509_, v_a_2515_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_funInfo_2530_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_synthInstance_2531_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_whnf_2532_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_defEqTrans_2533_);
lean_ctor_set(v_reuseFailAlloc_2548_, 5, v_defEqPerm_2534_);
v___x_2540_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2540_);
v___x_2542_ = v___x_2527_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_mctx_2522_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_zetaDeltaFVarIds_2523_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_postponed_2524_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v_diag_2525_);
v___x_2542_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_st_ref_put(v_a_2461_, v___x_2542_);
if (v_isShared_2519_ == 0)
{
v___x_2545_ = v___x_2518_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2515_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2515_);
lean_dec(v_a_2509_);
return v___x_2514_;
}
}
else
{
lean_dec(v_a_2509_);
return v___x_2514_;
}
}
v_resetjp_2555_:
{
lean_object* v_inferType_2558_; lean_object* v___x_2559_; 
v_inferType_2558_ = lean_ctor_get(v_cache_2554_, 0);
lean_inc_ref(v_inferType_2558_);
lean_dec_ref(v_cache_2554_);
lean_inc(v_a_2509_);
v___x_2559_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2506_, v___x_2507_, v_inferType_2558_, v_a_2509_);
lean_dec_ref(v_inferType_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2560_; lean_object* v_toApplicative_2561_; lean_object* v_toFunctor_2562_; lean_object* v_toSeq_2563_; lean_object* v_toSeqLeft_2564_; lean_object* v_toSeqRight_2565_; lean_object* v___f_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___x_2575_; 
lean_del_object(v___x_2511_);
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
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 4, v___f_2571_);
lean_ctor_set(v___x_2556_, 3, v___f_2572_);
lean_ctor_set(v___x_2556_, 2, v___f_2573_);
lean_ctor_set(v___x_2556_, 1, v___f_2566_);
lean_ctor_set(v___x_2556_, 0, v___x_2570_);
v___x_2575_ = v___x_2556_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___f_2566_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v___f_2573_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v___f_2572_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v___f_2571_);
v___x_2575_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_toCold_2582_; lean_object* v_cancelTk_x3f_2583_; 
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___f_2567_);
v___x_2577_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2578_ = l_Lean_Core_instMonadRefCoreM;
v___x_2579_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2580_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2579_, v___x_2576_);
v___x_2581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2577_);
lean_ctor_set(v___x_2581_, 1, v___x_2578_);
lean_ctor_set(v___x_2581_, 2, v___x_2580_);
v_toCold_2582_ = lean_ctor_get(v_a_2462_, 0);
v_cancelTk_x3f_2583_ = lean_ctor_get(v_toCold_2582_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2583_) == 1)
{
lean_object* v_val_2584_; uint8_t v___x_2585_; 
v_val_2584_ = lean_ctor_get(v_cancelTk_x3f_2583_, 0);
v___x_2585_ = l_IO_CancelToken_isSet(v_val_2584_);
if (v___x_2585_ == 0)
{
lean_dec_ref_known(v___x_2581_, 3);
goto v___jp_2513_;
}
else
{
lean_object* v___x_2058__overap_2586_; lean_object* v___x_2587_; 
v___x_2058__overap_2586_ = l_Lean_throwInterruptException___redArg(v___x_2581_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2587_ = lean_apply_3(v___x_2058__overap_2586_, v_a_2462_, v_a_2463_, lean_box(0));
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_dec_ref_known(v___x_2587_, 1);
goto v___jp_2513_;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_a_2509_);
lean_dec_ref(v_inferType_2459_);
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
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
}
else
{
lean_dec_ref_known(v___x_2581_, 3);
goto v___jp_2513_;
}
}
}
else
{
lean_object* v_val_2597_; lean_object* v___x_2599_; 
lean_del_object(v___x_2556_);
lean_dec(v_a_2509_);
lean_dec_ref(v_inferType_2459_);
v_val_2597_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v___x_2559_, 1);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v_val_2597_);
v___x_2599_ = v___x_2511_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_val_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_inferType_2459_);
v_a_2607_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2508_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2508_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_dec_ref(v_e_2458_);
goto v___jp_2465_;
}
}
v___jp_2465_:
{
lean_object* v___x_2466_; lean_object* v_toApplicative_2467_; lean_object* v_toFunctor_2468_; lean_object* v_toSeq_2469_; lean_object* v_toSeqLeft_2470_; lean_object* v_toSeqRight_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___f_2478_; lean_object* v___f_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_toCold_2487_; lean_object* v_cancelTk_x3f_2488_; 
v___x_2466_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2467_ = lean_ctor_get(v___x_2466_, 0);
v_toFunctor_2468_ = lean_ctor_get(v_toApplicative_2467_, 0);
v_toSeq_2469_ = lean_ctor_get(v_toApplicative_2467_, 2);
v_toSeqLeft_2470_ = lean_ctor_get(v_toApplicative_2467_, 3);
v_toSeqRight_2471_ = lean_ctor_get(v_toApplicative_2467_, 4);
v___f_2472_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2473_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2468_, 2);
v___f_2474_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2474_, 0, v_toFunctor_2468_);
v___f_2475_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2475_, 0, v_toFunctor_2468_);
v___x_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___f_2474_);
lean_ctor_set(v___x_2476_, 1, v___f_2475_);
lean_inc(v_toSeqRight_2471_);
v___f_2477_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2477_, 0, v_toSeqRight_2471_);
lean_inc(v_toSeqLeft_2470_);
v___f_2478_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2478_, 0, v_toSeqLeft_2470_);
lean_inc(v_toSeq_2469_);
v___f_2479_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2479_, 0, v_toSeq_2469_);
v___x_2480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2476_);
lean_ctor_set(v___x_2480_, 1, v___f_2472_);
lean_ctor_set(v___x_2480_, 2, v___f_2479_);
lean_ctor_set(v___x_2480_, 3, v___f_2478_);
lean_ctor_set(v___x_2480_, 4, v___f_2477_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___f_2473_);
v___x_2482_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2483_ = l_Lean_Core_instMonadRefCoreM;
v___x_2484_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2485_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2484_, v___x_2481_);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2482_);
lean_ctor_set(v___x_2486_, 1, v___x_2483_);
lean_ctor_set(v___x_2486_, 2, v___x_2485_);
v_toCold_2487_ = lean_ctor_get(v_a_2462_, 0);
v_cancelTk_x3f_2488_ = lean_ctor_get(v_toCold_2487_, 10);
if (lean_obj_tag(v_cancelTk_x3f_2488_) == 1)
{
lean_object* v_val_2489_; uint8_t v___x_2490_; 
v_val_2489_ = lean_ctor_get(v_cancelTk_x3f_2488_, 0);
v___x_2490_ = l_IO_CancelToken_isSet(v_val_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; 
lean_dec_ref_known(v___x_2486_, 3);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
v___x_2491_ = lean_apply_5(v_inferType_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, lean_box(0));
return v___x_2491_;
}
else
{
lean_object* v___x_2031__overap_2492_; lean_object* v___x_2493_; 
v___x_2031__overap_2492_ = l_Lean_throwInterruptException___redArg(v___x_2486_);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
v___x_2493_ = lean_apply_3(v___x_2031__overap_2492_, v_a_2462_, v_a_2463_, lean_box(0));
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref_known(v___x_2493_, 1);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
v___x_2494_ = lean_apply_5(v_inferType_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, lean_box(0));
return v___x_2494_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_inferType_2459_);
v_a_2495_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2493_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
else
{
lean_object* v___x_2503_; 
lean_dec_ref_known(v___x_2486_, 3);
lean_inc(v_a_2463_);
lean_inc_ref(v_a_2462_);
lean_inc(v_a_2461_);
lean_inc_ref(v_a_2460_);
v___x_2503_ = lean_apply_5(v_inferType_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, lean_box(0));
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2615_, lean_object* v_inferType_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2615_, v_inferType_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0(lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2675_; uint8_t v_beta_2676_; 
v___x_2675_ = l_Lean_Meta_Context_config(v___y_2624_);
v_beta_2676_ = lean_ctor_get_uint8(v___x_2675_, 13);
if (v_beta_2676_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_iota_2677_; 
v_iota_2677_ = lean_ctor_get_uint8(v___x_2675_, 12);
if (v_iota_2677_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_zeta_2678_; 
v_zeta_2678_ = lean_ctor_get_uint8(v___x_2675_, 15);
if (v_zeta_2678_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_zetaHave_2679_; 
v_zetaHave_2679_ = lean_ctor_get_uint8(v___x_2675_, 18);
if (v_zetaHave_2679_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_zetaDelta_2680_; 
v_zetaDelta_2680_ = lean_ctor_get_uint8(v___x_2675_, 16);
if (v_zetaDelta_2680_ == 0)
{
lean_dec_ref(v___x_2675_);
goto v___jp_2629_;
}
else
{
uint8_t v_etaStruct_2681_; uint8_t v_proj_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_etaStruct_2681_ = lean_ctor_get_uint8(v___x_2675_, 10);
v_proj_2682_ = lean_ctor_get_uint8(v___x_2675_, 14);
lean_dec_ref(v___x_2675_);
v___x_2683_ = lean_box(v_proj_2682_);
v___x_2684_ = lean_obj_tag_nat(v___x_2683_);
lean_dec(v___x_2683_);
v___x_2685_ = lean_unsigned_to_nat(2u);
v___x_2686_ = lean_nat_dec_eq(v___x_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
goto v___jp_2629_;
}
else
{
uint8_t v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = 0;
v___x_2688_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2681_, v___x_2687_);
if (v___x_2688_ == 0)
{
goto v___jp_2629_;
}
else
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_apply_5(v_x_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, lean_box(0));
return v___x_2689_;
}
}
}
}
}
}
}
v___jp_2629_:
{
lean_object* v___x_2630_; uint8_t v_foApprox_2631_; uint8_t v_ctxApprox_2632_; uint8_t v_quasiPatternApprox_2633_; uint8_t v_constApprox_2634_; uint8_t v_isDefEqStuckEx_2635_; uint8_t v_unificationHints_2636_; uint8_t v_proofIrrelevance_2637_; uint8_t v_assignSyntheticOpaque_2638_; uint8_t v_offsetCnstrs_2639_; uint8_t v_transparency_2640_; uint8_t v_univApprox_2641_; uint8_t v_zetaUnused_2642_; uint8_t v_canUnfoldPredicateConfig_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2674_; 
v___x_2630_ = l_Lean_Meta_Context_config(v___y_2624_);
v_foApprox_2631_ = lean_ctor_get_uint8(v___x_2630_, 0);
v_ctxApprox_2632_ = lean_ctor_get_uint8(v___x_2630_, 1);
v_quasiPatternApprox_2633_ = lean_ctor_get_uint8(v___x_2630_, 2);
v_constApprox_2634_ = lean_ctor_get_uint8(v___x_2630_, 3);
v_isDefEqStuckEx_2635_ = lean_ctor_get_uint8(v___x_2630_, 4);
v_unificationHints_2636_ = lean_ctor_get_uint8(v___x_2630_, 5);
v_proofIrrelevance_2637_ = lean_ctor_get_uint8(v___x_2630_, 6);
v_assignSyntheticOpaque_2638_ = lean_ctor_get_uint8(v___x_2630_, 7);
v_offsetCnstrs_2639_ = lean_ctor_get_uint8(v___x_2630_, 8);
v_transparency_2640_ = lean_ctor_get_uint8(v___x_2630_, 9);
v_univApprox_2641_ = lean_ctor_get_uint8(v___x_2630_, 11);
v_zetaUnused_2642_ = lean_ctor_get_uint8(v___x_2630_, 17);
v_canUnfoldPredicateConfig_2643_ = lean_ctor_get_uint8(v___x_2630_, 19);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2645_ = v___x_2630_;
v_isShared_2646_ = v_isSharedCheck_2674_;
goto v_resetjp_2644_;
}
else
{
lean_dec(v___x_2630_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2674_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
uint8_t v___x_2647_; uint8_t v___x_2648_; uint8_t v___x_2649_; lean_object* v___x_2651_; 
v___x_2647_ = 1;
v___x_2648_ = 0;
v___x_2649_ = 2;
if (v_isShared_2646_ == 0)
{
v___x_2651_ = v___x_2645_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 0, v_foApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 1, v_ctxApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 2, v_quasiPatternApprox_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 3, v_constApprox_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 4, v_isDefEqStuckEx_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 5, v_unificationHints_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 6, v_proofIrrelevance_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 7, v_assignSyntheticOpaque_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 8, v_offsetCnstrs_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 9, v_transparency_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 11, v_univApprox_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 17, v_zetaUnused_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, 19, v_canUnfoldPredicateConfig_2643_);
v___x_2651_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
uint8_t v_trackZetaDelta_2652_; lean_object* v_zetaDeltaSet_2653_; lean_object* v_lctx_2654_; lean_object* v_localInstances_2655_; lean_object* v_defEqCtx_x3f_2656_; lean_object* v_synthPendingDepth_2657_; lean_object* v_customCanUnfoldPredicate_x3f_2658_; uint8_t v_univApprox_2659_; uint8_t v_inTypeClassResolution_2660_; uint8_t v_cacheInferType_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2671_; 
lean_ctor_set_uint8(v___x_2651_, 10, v___x_2648_);
lean_ctor_set_uint8(v___x_2651_, 12, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 13, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 14, v___x_2649_);
lean_ctor_set_uint8(v___x_2651_, 15, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 16, v___x_2647_);
lean_ctor_set_uint8(v___x_2651_, 18, v___x_2647_);
v_trackZetaDelta_2652_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7);
v_zetaDeltaSet_2653_ = lean_ctor_get(v___y_2624_, 1);
v_lctx_2654_ = lean_ctor_get(v___y_2624_, 2);
v_localInstances_2655_ = lean_ctor_get(v___y_2624_, 3);
v_defEqCtx_x3f_2656_ = lean_ctor_get(v___y_2624_, 4);
v_synthPendingDepth_2657_ = lean_ctor_get(v___y_2624_, 5);
v_customCanUnfoldPredicate_x3f_2658_ = lean_ctor_get(v___y_2624_, 6);
v_univApprox_2659_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2660_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7 + 2);
v_cacheInferType_2661_ = lean_ctor_get_uint8(v___y_2624_, sizeof(void*)*7 + 3);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___y_2624_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___y_2624_, 0);
lean_dec(v_unused_2672_);
v___x_2663_ = v___y_2624_;
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_2658_);
lean_inc(v_synthPendingDepth_2657_);
lean_inc(v_defEqCtx_x3f_2656_);
lean_inc(v_localInstances_2655_);
lean_inc(v_lctx_2654_);
lean_inc(v_zetaDeltaSet_2653_);
lean_dec(v___y_2624_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
uint64_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2651_);
v___x_2666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2666_, 0, v___x_2651_);
lean_ctor_set_uint64(v___x_2666_, sizeof(void*)*1, v___x_2665_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2666_);
v___x_2668_ = v___x_2663_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_zetaDeltaSet_2653_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_lctx_2654_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_localInstances_2655_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_defEqCtx_x3f_2656_);
lean_ctor_set(v_reuseFailAlloc_2670_, 5, v_synthPendingDepth_2657_);
lean_ctor_set(v_reuseFailAlloc_2670_, 6, v_customCanUnfoldPredicate_x3f_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7, v_trackZetaDelta_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 1, v_univApprox_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 3, v_cacheInferType_2661_);
v___x_2668_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_apply_5(v_x_2623_, v___x_2668_, v___y_2625_, v___y_2626_, v___y_2627_, lean_box(0));
return v___x_2669_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___lam__0___boxed(lean_object* v_x_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v___y_2704_; lean_object* v___x_2721_; uint8_t v_transparency_2722_; uint8_t v___x_2723_; uint8_t v___x_2724_; 
v___x_2721_ = l_Lean_Meta_Context_config(v_a_2698_);
v_transparency_2722_ = lean_ctor_get_uint8(v___x_2721_, 9);
lean_dec_ref(v___x_2721_);
v___x_2723_ = 1;
v___x_2724_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2722_, v___x_2723_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
lean_inc(v_a_2701_);
lean_inc_ref(v_a_2700_);
lean_inc(v_a_2699_);
lean_inc_ref(v_a_2698_);
v___x_2725_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
v___y_2704_ = v___x_2725_;
goto v___jp_2703_;
}
else
{
lean_object* v_keyedConfig_2726_; uint8_t v_trackZetaDelta_2727_; lean_object* v_zetaDeltaSet_2728_; lean_object* v_lctx_2729_; lean_object* v_localInstances_2730_; lean_object* v_defEqCtx_x3f_2731_; lean_object* v_synthPendingDepth_2732_; lean_object* v_customCanUnfoldPredicate_x3f_2733_; uint8_t v_univApprox_2734_; uint8_t v_inTypeClassResolution_2735_; uint8_t v_cacheInferType_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_keyedConfig_2726_ = lean_ctor_get(v_a_2698_, 0);
v_trackZetaDelta_2727_ = lean_ctor_get_uint8(v_a_2698_, sizeof(void*)*7);
v_zetaDeltaSet_2728_ = lean_ctor_get(v_a_2698_, 1);
v_lctx_2729_ = lean_ctor_get(v_a_2698_, 2);
v_localInstances_2730_ = lean_ctor_get(v_a_2698_, 3);
v_defEqCtx_x3f_2731_ = lean_ctor_get(v_a_2698_, 4);
v_synthPendingDepth_2732_ = lean_ctor_get(v_a_2698_, 5);
v_customCanUnfoldPredicate_x3f_2733_ = lean_ctor_get(v_a_2698_, 6);
v_univApprox_2734_ = lean_ctor_get_uint8(v_a_2698_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2735_ = lean_ctor_get_uint8(v_a_2698_, sizeof(void*)*7 + 2);
v_cacheInferType_2736_ = lean_ctor_get_uint8(v_a_2698_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2726_);
v___x_2737_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2723_, v_keyedConfig_2726_);
lean_inc(v_customCanUnfoldPredicate_x3f_2733_);
lean_inc(v_synthPendingDepth_2732_);
lean_inc(v_defEqCtx_x3f_2731_);
lean_inc_ref(v_localInstances_2730_);
lean_inc_ref(v_lctx_2729_);
lean_inc(v_zetaDeltaSet_2728_);
v___x_2738_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v_zetaDeltaSet_2728_);
lean_ctor_set(v___x_2738_, 2, v_lctx_2729_);
lean_ctor_set(v___x_2738_, 3, v_localInstances_2730_);
lean_ctor_set(v___x_2738_, 4, v_defEqCtx_x3f_2731_);
lean_ctor_set(v___x_2738_, 5, v_synthPendingDepth_2732_);
lean_ctor_set(v___x_2738_, 6, v_customCanUnfoldPredicate_x3f_2733_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7, v_trackZetaDelta_2727_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7 + 1, v_univApprox_2734_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2735_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7 + 3, v_cacheInferType_2736_);
lean_inc(v_a_2701_);
lean_inc_ref(v_a_2700_);
lean_inc(v_a_2699_);
v___x_2739_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2697_, v___x_2738_, v_a_2699_, v_a_2700_, v_a_2701_);
v___y_2704_ = v___x_2739_;
goto v___jp_2703_;
}
v___jp_2703_:
{
if (lean_obj_tag(v___y_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
v_a_2705_ = lean_ctor_get(v___y_2704_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___y_2704_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___y_2704_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___y_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v___y_2704_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___y_2704_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___y_2704_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___y_2704_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2747_, lean_object* v_x_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v___y_2755_; lean_object* v___x_2772_; uint8_t v_transparency_2773_; uint8_t v___x_2774_; uint8_t v___x_2775_; 
v___x_2772_ = l_Lean_Meta_Context_config(v_a_2749_);
v_transparency_2773_ = lean_ctor_get_uint8(v___x_2772_, 9);
lean_dec_ref(v___x_2772_);
v___x_2774_ = 1;
v___x_2775_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2773_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; 
lean_inc(v_a_2752_);
lean_inc_ref(v_a_2751_);
lean_inc(v_a_2750_);
lean_inc_ref(v_a_2749_);
v___x_2776_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
v___y_2755_ = v___x_2776_;
goto v___jp_2754_;
}
else
{
lean_object* v_keyedConfig_2777_; uint8_t v_trackZetaDelta_2778_; lean_object* v_zetaDeltaSet_2779_; lean_object* v_lctx_2780_; lean_object* v_localInstances_2781_; lean_object* v_defEqCtx_x3f_2782_; lean_object* v_synthPendingDepth_2783_; lean_object* v_customCanUnfoldPredicate_x3f_2784_; uint8_t v_univApprox_2785_; uint8_t v_inTypeClassResolution_2786_; uint8_t v_cacheInferType_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_keyedConfig_2777_ = lean_ctor_get(v_a_2749_, 0);
v_trackZetaDelta_2778_ = lean_ctor_get_uint8(v_a_2749_, sizeof(void*)*7);
v_zetaDeltaSet_2779_ = lean_ctor_get(v_a_2749_, 1);
v_lctx_2780_ = lean_ctor_get(v_a_2749_, 2);
v_localInstances_2781_ = lean_ctor_get(v_a_2749_, 3);
v_defEqCtx_x3f_2782_ = lean_ctor_get(v_a_2749_, 4);
v_synthPendingDepth_2783_ = lean_ctor_get(v_a_2749_, 5);
v_customCanUnfoldPredicate_x3f_2784_ = lean_ctor_get(v_a_2749_, 6);
v_univApprox_2785_ = lean_ctor_get_uint8(v_a_2749_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2786_ = lean_ctor_get_uint8(v_a_2749_, sizeof(void*)*7 + 2);
v_cacheInferType_2787_ = lean_ctor_get_uint8(v_a_2749_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2777_);
v___x_2788_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2774_, v_keyedConfig_2777_);
lean_inc(v_customCanUnfoldPredicate_x3f_2784_);
lean_inc(v_synthPendingDepth_2783_);
lean_inc(v_defEqCtx_x3f_2782_);
lean_inc_ref(v_localInstances_2781_);
lean_inc_ref(v_lctx_2780_);
lean_inc(v_zetaDeltaSet_2779_);
v___x_2789_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v_zetaDeltaSet_2779_);
lean_ctor_set(v___x_2789_, 2, v_lctx_2780_);
lean_ctor_set(v___x_2789_, 3, v_localInstances_2781_);
lean_ctor_set(v___x_2789_, 4, v_defEqCtx_x3f_2782_);
lean_ctor_set(v___x_2789_, 5, v_synthPendingDepth_2783_);
lean_ctor_set(v___x_2789_, 6, v_customCanUnfoldPredicate_x3f_2784_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*7, v_trackZetaDelta_2778_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*7 + 1, v_univApprox_2785_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2786_);
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*7 + 3, v_cacheInferType_2787_);
lean_inc(v_a_2752_);
lean_inc_ref(v_a_2751_);
lean_inc(v_a_2750_);
v___x_2790_ = l_Lean_Meta_withInferTypeConfig___redArg___lam__0(v_x_2748_, v___x_2789_, v_a_2750_, v_a_2751_, v_a_2752_);
v___y_2755_ = v___x_2790_;
goto v___jp_2754_;
}
v___jp_2754_:
{
if (lean_obj_tag(v___y_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
v_a_2756_ = lean_ctor_get(v___y_2755_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___y_2755_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___y_2755_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___y_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v_a_2764_ = lean_ctor_get(v___y_2755_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___y_2755_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___y_2755_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___y_2755_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2791_, lean_object* v_x_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2791_, v_x_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
return v_res_2798_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_box(0);
v___x_2800_ = l_Lean_interruptExceptionId;
v___x_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___x_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v_x_2820_){
_start:
{
lean_object* v_ks_2821_; lean_object* v_vs_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2851_; 
v_ks_2821_ = lean_ctor_get(v_x_2817_, 0);
v_vs_2822_ = lean_ctor_get(v_x_2817_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2824_ = v_x_2817_;
v_isShared_2825_ = v_isSharedCheck_2851_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_vs_2822_);
lean_inc(v_ks_2821_);
lean_dec(v_x_2817_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2851_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
uint8_t v___y_2827_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = lean_array_get_size(v_ks_2821_);
v___x_2840_ = lean_nat_dec_lt(v_x_2818_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_del_object(v___x_2824_);
lean_dec(v_x_2818_);
v___x_2841_ = lean_array_push(v_ks_2821_, v_x_2819_);
v___x_2842_ = lean_array_push(v_vs_2822_, v_x_2820_);
v___x_2843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
return v___x_2843_;
}
else
{
lean_object* v_expr_2844_; uint64_t v_configKey_2845_; lean_object* v_k_x27_2846_; lean_object* v_expr_2847_; uint64_t v_configKey_2848_; uint8_t v___x_2849_; 
v_expr_2844_ = lean_ctor_get(v_x_2819_, 0);
v_configKey_2845_ = lean_ctor_get_uint64(v_x_2819_, sizeof(void*)*1);
v_k_x27_2846_ = lean_array_fget_borrowed(v_ks_2821_, v_x_2818_);
v_expr_2847_ = lean_ctor_get(v_k_x27_2846_, 0);
v_configKey_2848_ = lean_ctor_get_uint64(v_k_x27_2846_, sizeof(void*)*1);
v___x_2849_ = lean_expr_equal(v_expr_2844_, v_expr_2847_);
if (v___x_2849_ == 0)
{
v___y_2827_ = v___x_2849_;
goto v___jp_2826_;
}
else
{
uint8_t v___x_2850_; 
v___x_2850_ = lean_uint64_dec_eq(v_configKey_2845_, v_configKey_2848_);
v___y_2827_ = v___x_2850_;
goto v___jp_2826_;
}
}
v___jp_2826_:
{
if (v___y_2827_ == 0)
{
lean_object* v___x_2829_; 
if (v_isShared_2825_ == 0)
{
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_ks_2821_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_vs_2822_);
v___x_2829_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_unsigned_to_nat(1u);
v___x_2831_ = lean_nat_add(v_x_2818_, v___x_2830_);
lean_dec(v_x_2818_);
v_x_2817_ = v___x_2829_;
v_x_2818_ = v___x_2831_;
goto _start;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2834_ = lean_array_fset(v_ks_2821_, v_x_2818_, v_x_2819_);
v___x_2835_ = lean_array_fset(v_vs_2822_, v_x_2818_, v_x_2820_);
lean_dec(v_x_2818_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 1, v___x_2835_);
lean_ctor_set(v___x_2824_, 0, v___x_2834_);
v___x_2837_ = v___x_2824_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v___x_2835_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2852_, lean_object* v_k_2853_, lean_object* v_v_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_unsigned_to_nat(0u);
v___x_2856_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2852_, v___x_2855_, v_k_2853_, v_v_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2857_, size_t v_x_2858_, size_t v_x_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_){
_start:
{
if (lean_obj_tag(v_x_2857_) == 0)
{
lean_object* v_es_2862_; size_t v___x_2863_; size_t v___x_2864_; lean_object* v_j_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_es_2862_ = lean_ctor_get(v_x_2857_, 0);
v___x_2863_ = ((size_t)31ULL);
v___x_2864_ = lean_usize_land(v_x_2858_, v___x_2863_);
v_j_2865_ = lean_usize_to_nat(v___x_2864_);
v___x_2866_ = lean_array_get_size(v_es_2862_);
v___x_2867_ = lean_nat_dec_lt(v_j_2865_, v___x_2866_);
if (v___x_2867_ == 0)
{
lean_dec(v_j_2865_);
lean_dec(v_x_2861_);
lean_dec_ref(v_x_2860_);
return v_x_2857_;
}
else
{
lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2913_; 
lean_inc_ref(v_es_2862_);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_x_2857_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v_x_2857_, 0);
lean_dec(v_unused_2914_);
v___x_2869_ = v_x_2857_;
v_isShared_2870_ = v_isSharedCheck_2913_;
goto v_resetjp_2868_;
}
else
{
lean_dec(v_x_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2913_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v_v_2871_; lean_object* v___x_2872_; lean_object* v_xs_x27_2873_; lean_object* v___y_2875_; 
v_v_2871_ = lean_array_fget(v_es_2862_, v_j_2865_);
v___x_2872_ = lean_box(0);
v_xs_x27_2873_ = lean_array_fset(v_es_2862_, v_j_2865_, v___x_2872_);
switch(lean_obj_tag(v_v_2871_))
{
case 0:
{
lean_object* v_key_2880_; lean_object* v_val_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2898_; 
v_key_2880_ = lean_ctor_get(v_v_2871_, 0);
v_val_2881_ = lean_ctor_get(v_v_2871_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_v_2871_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2883_ = v_v_2871_;
v_isShared_2884_ = v_isSharedCheck_2898_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_val_2881_);
lean_inc(v_key_2880_);
lean_dec(v_v_2871_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2898_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
uint8_t v___y_2886_; lean_object* v_expr_2892_; uint64_t v_configKey_2893_; lean_object* v_expr_2894_; uint64_t v_configKey_2895_; uint8_t v___x_2896_; 
v_expr_2892_ = lean_ctor_get(v_x_2860_, 0);
v_configKey_2893_ = lean_ctor_get_uint64(v_x_2860_, sizeof(void*)*1);
v_expr_2894_ = lean_ctor_get(v_key_2880_, 0);
v_configKey_2895_ = lean_ctor_get_uint64(v_key_2880_, sizeof(void*)*1);
v___x_2896_ = lean_expr_equal(v_expr_2892_, v_expr_2894_);
if (v___x_2896_ == 0)
{
v___y_2886_ = v___x_2896_;
goto v___jp_2885_;
}
else
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_uint64_dec_eq(v_configKey_2893_, v_configKey_2895_);
v___y_2886_ = v___x_2897_;
goto v___jp_2885_;
}
v___jp_2885_:
{
if (v___y_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_del_object(v___x_2883_);
v___x_2887_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2880_, v_val_2881_, v_x_2860_, v_x_2861_);
v___x_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
v___y_2875_ = v___x_2888_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2890_; 
lean_dec(v_val_2881_);
lean_dec(v_key_2880_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 1, v_x_2861_);
lean_ctor_set(v___x_2883_, 0, v_x_2860_);
v___x_2890_ = v___x_2883_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_x_2860_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_x_2861_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
v___y_2875_ = v___x_2890_;
goto v___jp_2874_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2911_; 
v_node_2899_ = lean_ctor_get(v_v_2871_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_v_2871_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2901_ = v_v_2871_;
v_isShared_2902_ = v_isSharedCheck_2911_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_node_2899_);
lean_dec(v_v_2871_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2911_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
size_t v___x_2903_; size_t v___x_2904_; size_t v___x_2905_; size_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2903_ = ((size_t)5ULL);
v___x_2904_ = lean_usize_shift_right(v_x_2858_, v___x_2903_);
v___x_2905_ = ((size_t)1ULL);
v___x_2906_ = lean_usize_add(v_x_2859_, v___x_2905_);
v___x_2907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2899_, v___x_2904_, v___x_2906_, v_x_2860_, v_x_2861_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2907_);
v___x_2909_ = v___x_2901_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
v___y_2875_ = v___x_2909_;
goto v___jp_2874_;
}
}
}
default: 
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_x_2860_);
lean_ctor_set(v___x_2912_, 1, v_x_2861_);
v___y_2875_ = v___x_2912_;
goto v___jp_2874_;
}
}
v___jp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = lean_array_fset(v_xs_x27_2873_, v_j_2865_, v___y_2875_);
lean_dec(v_j_2865_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2876_);
v___x_2878_ = v___x_2869_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_object* v_ks_2915_; lean_object* v_vs_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2934_; 
v_ks_2915_ = lean_ctor_get(v_x_2857_, 0);
v_vs_2916_ = lean_ctor_get(v_x_2857_, 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_x_2857_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2918_ = v_x_2857_;
v_isShared_2919_ = v_isSharedCheck_2934_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_vs_2916_);
lean_inc(v_ks_2915_);
lean_dec(v_x_2857_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2934_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_ks_2915_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_vs_2916_);
v___x_2921_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v_newNode_2922_; size_t v___x_2923_; uint8_t v___x_2924_; 
v_newNode_2922_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2921_, v_x_2860_, v_x_2861_);
v___x_2923_ = ((size_t)7ULL);
v___x_2924_ = lean_usize_dec_le(v___x_2923_, v_x_2859_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2925_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2922_);
v___x_2926_ = lean_unsigned_to_nat(4u);
v___x_2927_ = lean_nat_dec_lt(v___x_2925_, v___x_2926_);
lean_dec(v___x_2925_);
if (v___x_2927_ == 0)
{
lean_object* v_ks_2928_; lean_object* v_vs_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v_ks_2928_ = lean_ctor_get(v_newNode_2922_, 0);
lean_inc_ref(v_ks_2928_);
v_vs_2929_ = lean_ctor_get(v_newNode_2922_, 1);
lean_inc_ref(v_vs_2929_);
lean_dec_ref(v_newNode_2922_);
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_2932_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2859_, v_ks_2928_, v_vs_2929_, v___x_2930_, v___x_2931_);
lean_dec_ref(v_vs_2929_);
lean_dec_ref(v_ks_2928_);
return v___x_2932_;
}
else
{
return v_newNode_2922_;
}
}
else
{
return v_newNode_2922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2935_, lean_object* v_keys_2936_, lean_object* v_vals_2937_, lean_object* v_i_2938_, lean_object* v_entries_2939_){
_start:
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_keys_2936_);
v___x_2941_ = lean_nat_dec_lt(v_i_2938_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_dec(v_i_2938_);
return v_entries_2939_;
}
else
{
lean_object* v_k_2942_; lean_object* v_expr_2943_; uint64_t v_configKey_2944_; lean_object* v_v_2945_; uint64_t v___x_2946_; uint64_t v___x_2947_; size_t v_h_2948_; size_t v___x_2949_; lean_object* v___x_2950_; size_t v___x_2951_; size_t v___x_2952_; size_t v___x_2953_; size_t v_h_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_k_2942_ = lean_array_fget_borrowed(v_keys_2936_, v_i_2938_);
v_expr_2943_ = lean_ctor_get(v_k_2942_, 0);
v_configKey_2944_ = lean_ctor_get_uint64(v_k_2942_, sizeof(void*)*1);
v_v_2945_ = lean_array_fget_borrowed(v_vals_2937_, v_i_2938_);
v___x_2946_ = l_Lean_Expr_hash(v_expr_2943_);
v___x_2947_ = lean_uint64_mix_hash(v___x_2946_, v_configKey_2944_);
v_h_2948_ = lean_uint64_to_usize(v___x_2947_);
v___x_2949_ = ((size_t)5ULL);
v___x_2950_ = lean_unsigned_to_nat(1u);
v___x_2951_ = ((size_t)1ULL);
v___x_2952_ = lean_usize_sub(v_depth_2935_, v___x_2951_);
v___x_2953_ = lean_usize_mul(v___x_2949_, v___x_2952_);
v_h_2954_ = lean_usize_shift_right(v_h_2948_, v___x_2953_);
v___x_2955_ = lean_nat_add(v_i_2938_, v___x_2950_);
lean_dec(v_i_2938_);
lean_inc(v_v_2945_);
lean_inc(v_k_2942_);
v___x_2956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2939_, v_h_2954_, v_depth_2935_, v_k_2942_, v_v_2945_);
v_i_2938_ = v___x_2955_;
v_entries_2939_ = v___x_2956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2958_, lean_object* v_keys_2959_, lean_object* v_vals_2960_, lean_object* v_i_2961_, lean_object* v_entries_2962_){
_start:
{
size_t v_depth_boxed_2963_; lean_object* v_res_2964_; 
v_depth_boxed_2963_ = lean_unbox_usize(v_depth_2958_);
lean_dec(v_depth_2958_);
v_res_2964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2963_, v_keys_2959_, v_vals_2960_, v_i_2961_, v_entries_2962_);
lean_dec_ref(v_vals_2960_);
lean_dec_ref(v_keys_2959_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_){
_start:
{
size_t v_x_2395__boxed_2970_; size_t v_x_2396__boxed_2971_; lean_object* v_res_2972_; 
v_x_2395__boxed_2970_ = lean_unbox_usize(v_x_2966_);
lean_dec(v_x_2966_);
v_x_2396__boxed_2971_ = lean_unbox_usize(v_x_2967_);
lean_dec(v_x_2967_);
v_res_2972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2965_, v_x_2395__boxed_2970_, v_x_2396__boxed_2971_, v_x_2968_, v_x_2969_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_){
_start:
{
lean_object* v_expr_2976_; uint64_t v_configKey_2977_; uint64_t v___x_2978_; uint64_t v___x_2979_; size_t v___x_2980_; size_t v___x_2981_; lean_object* v___x_2982_; 
v_expr_2976_ = lean_ctor_get(v_x_2974_, 0);
v_configKey_2977_ = lean_ctor_get_uint64(v_x_2974_, sizeof(void*)*1);
v___x_2978_ = l_Lean_Expr_hash(v_expr_2976_);
v___x_2979_ = lean_uint64_mix_hash(v___x_2978_, v_configKey_2977_);
v___x_2980_ = lean_uint64_to_usize(v___x_2979_);
v___x_2981_ = ((size_t)1ULL);
v___x_2982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2973_, v___x_2980_, v___x_2981_, v_x_2974_, v_x_2975_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2983_, lean_object* v_vals_2984_, lean_object* v_i_2985_, lean_object* v_k_2986_){
_start:
{
uint8_t v___y_2988_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = lean_array_get_size(v_keys_2983_);
v___x_2995_ = lean_nat_dec_lt(v_i_2985_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v_i_2985_);
v___x_2996_ = lean_box(0);
return v___x_2996_;
}
else
{
lean_object* v_expr_2997_; uint64_t v_configKey_2998_; lean_object* v_k_x27_2999_; lean_object* v_expr_3000_; uint64_t v_configKey_3001_; uint8_t v___x_3002_; 
v_expr_2997_ = lean_ctor_get(v_k_2986_, 0);
v_configKey_2998_ = lean_ctor_get_uint64(v_k_2986_, sizeof(void*)*1);
v_k_x27_2999_ = lean_array_fget_borrowed(v_keys_2983_, v_i_2985_);
v_expr_3000_ = lean_ctor_get(v_k_x27_2999_, 0);
v_configKey_3001_ = lean_ctor_get_uint64(v_k_x27_2999_, sizeof(void*)*1);
v___x_3002_ = lean_expr_equal(v_expr_2997_, v_expr_3000_);
if (v___x_3002_ == 0)
{
v___y_2988_ = v___x_3002_;
goto v___jp_2987_;
}
else
{
uint8_t v___x_3003_; 
v___x_3003_ = lean_uint64_dec_eq(v_configKey_2998_, v_configKey_3001_);
v___y_2988_ = v___x_3003_;
goto v___jp_2987_;
}
}
v___jp_2987_:
{
if (v___y_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_unsigned_to_nat(1u);
v___x_2990_ = lean_nat_add(v_i_2985_, v___x_2989_);
lean_dec(v_i_2985_);
v_i_2985_ = v___x_2990_;
goto _start;
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_array_fget_borrowed(v_vals_2984_, v_i_2985_);
lean_dec(v_i_2985_);
lean_inc(v___x_2992_);
v___x_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3004_, lean_object* v_vals_3005_, lean_object* v_i_3006_, lean_object* v_k_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3004_, v_vals_3005_, v_i_3006_, v_k_3007_);
lean_dec_ref(v_k_3007_);
lean_dec_ref(v_vals_3005_);
lean_dec_ref(v_keys_3004_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3009_, size_t v_x_3010_, lean_object* v_x_3011_){
_start:
{
if (lean_obj_tag(v_x_3009_) == 0)
{
lean_object* v_es_3012_; lean_object* v___x_3013_; size_t v___x_3014_; size_t v___x_3015_; lean_object* v_j_3016_; lean_object* v___x_3017_; 
v_es_3012_ = lean_ctor_get(v_x_3009_, 0);
v___x_3013_ = lean_box(2);
v___x_3014_ = ((size_t)31ULL);
v___x_3015_ = lean_usize_land(v_x_3010_, v___x_3014_);
v_j_3016_ = lean_usize_to_nat(v___x_3015_);
v___x_3017_ = lean_array_get_borrowed(v___x_3013_, v_es_3012_, v_j_3016_);
lean_dec(v_j_3016_);
switch(lean_obj_tag(v___x_3017_))
{
case 0:
{
lean_object* v_key_3018_; lean_object* v_val_3019_; uint8_t v___y_3021_; lean_object* v_expr_3024_; uint64_t v_configKey_3025_; lean_object* v_expr_3026_; uint64_t v_configKey_3027_; uint8_t v___x_3028_; 
v_key_3018_ = lean_ctor_get(v___x_3017_, 0);
v_val_3019_ = lean_ctor_get(v___x_3017_, 1);
v_expr_3024_ = lean_ctor_get(v_x_3011_, 0);
v_configKey_3025_ = lean_ctor_get_uint64(v_x_3011_, sizeof(void*)*1);
v_expr_3026_ = lean_ctor_get(v_key_3018_, 0);
v_configKey_3027_ = lean_ctor_get_uint64(v_key_3018_, sizeof(void*)*1);
v___x_3028_ = lean_expr_equal(v_expr_3024_, v_expr_3026_);
if (v___x_3028_ == 0)
{
v___y_3021_ = v___x_3028_;
goto v___jp_3020_;
}
else
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_uint64_dec_eq(v_configKey_3025_, v_configKey_3027_);
v___y_3021_ = v___x_3029_;
goto v___jp_3020_;
}
v___jp_3020_:
{
if (v___y_3021_ == 0)
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_box(0);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; 
lean_inc(v_val_3019_);
v___x_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_val_3019_);
return v___x_3023_;
}
}
}
case 1:
{
lean_object* v_node_3030_; size_t v___x_3031_; size_t v___x_3032_; 
v_node_3030_ = lean_ctor_get(v___x_3017_, 0);
v___x_3031_ = ((size_t)5ULL);
v___x_3032_ = lean_usize_shift_right(v_x_3010_, v___x_3031_);
v_x_3009_ = v_node_3030_;
v_x_3010_ = v___x_3032_;
goto _start;
}
default: 
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_box(0);
return v___x_3034_;
}
}
}
else
{
lean_object* v_ks_3035_; lean_object* v_vs_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_ks_3035_ = lean_ctor_get(v_x_3009_, 0);
v_vs_3036_ = lean_ctor_get(v_x_3009_, 1);
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3035_, v_vs_3036_, v___x_3037_, v_x_3011_);
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
size_t v_x_2599__boxed_3042_; lean_object* v_res_3043_; 
v_x_2599__boxed_3042_ = lean_unbox_usize(v_x_3040_);
lean_dec(v_x_3040_);
v_res_3043_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3039_, v_x_2599__boxed_3042_, v_x_3041_);
lean_dec_ref(v_x_3041_);
lean_dec_ref(v_x_3039_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3044_, lean_object* v_x_3045_){
_start:
{
lean_object* v_expr_3046_; uint64_t v_configKey_3047_; uint64_t v___x_3048_; uint64_t v___x_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v_expr_3046_ = lean_ctor_get(v_x_3045_, 0);
v_configKey_3047_ = lean_ctor_get_uint64(v_x_3045_, sizeof(void*)*1);
v___x_3048_ = l_Lean_Expr_hash(v_expr_3046_);
v___x_3049_ = lean_uint64_mix_hash(v___x_3048_, v_configKey_3047_);
v___x_3050_ = lean_uint64_to_usize(v___x_3049_);
v___x_3051_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3044_, v___x_3050_, v_x_3045_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3052_, lean_object* v_x_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3052_, v_x_3053_);
lean_dec_ref(v_x_3053_);
lean_dec_ref(v_x_3052_);
return v_res_3054_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3057_ = l_Lean_stringToMessageData(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
switch(lean_obj_tag(v_e_3058_))
{
case 0:
{
lean_object* v_deBruijnIndex_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_deBruijnIndex_3096_ = lean_ctor_get(v_e_3058_, 0);
lean_inc(v_deBruijnIndex_3096_);
lean_dec_ref_known(v_e_3058_, 1);
v___x_3097_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3098_ = l_Lean_mkBVar(v_deBruijnIndex_3096_);
v___x_3099_ = l_Lean_MessageData_ofExpr(v___x_3098_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3097_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3100_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3101_;
}
case 1:
{
lean_object* v_fvarId_3102_; lean_object* v___x_3103_; 
v_fvarId_3102_ = lean_ctor_get(v_e_3058_, 0);
lean_inc(v_fvarId_3102_);
lean_dec_ref_known(v_e_3058_, 1);
v___x_3103_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3102_, v_a_3059_, v_a_3061_, v_a_3062_);
return v___x_3103_;
}
case 2:
{
lean_object* v_mvarId_3104_; lean_object* v___x_3105_; 
v_mvarId_3104_ = lean_ctor_get(v_e_3058_, 0);
lean_inc(v_mvarId_3104_);
lean_dec_ref_known(v_e_3058_, 1);
v___x_3105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3104_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3105_;
}
case 3:
{
lean_object* v_u_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_u_3106_ = lean_ctor_get(v_e_3058_, 0);
lean_inc(v_u_3106_);
lean_dec_ref_known(v_e_3058_, 1);
v___x_3107_ = l_Lean_Level_succ___override(v_u_3106_);
v___x_3108_ = l_Lean_mkSort(v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
case 4:
{
lean_object* v_declName_3110_; lean_object* v_us_3111_; 
v_declName_3110_ = lean_ctor_get(v_e_3058_, 0);
lean_inc(v_declName_3110_);
v_us_3111_ = lean_ctor_get(v_e_3058_, 1);
lean_inc(v_us_3111_);
if (lean_obj_tag(v_us_3111_) == 0)
{
lean_object* v___x_3128_; 
lean_dec_ref_known(v_e_3058_, 2);
v___x_3128_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3110_, v_us_3111_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3128_;
}
else
{
uint8_t v_cacheInferType_3129_; 
v_cacheInferType_3129_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3129_ == 0)
{
lean_dec_ref_known(v_e_3058_, 2);
goto v___jp_3112_;
}
else
{
uint8_t v___x_3130_; 
v___x_3130_ = l_Lean_Expr_hasMVar(v_e_3058_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3197_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3197_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3197_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3176_; lean_object* v_cache_3177_; lean_object* v_inferType_3178_; lean_object* v___x_3179_; 
v___x_3176_ = lean_st_ref_get(v_a_3060_);
v_cache_3177_ = lean_ctor_get(v___x_3176_, 1);
lean_inc_ref(v_cache_3177_);
lean_dec(v___x_3176_);
v_inferType_3178_ = lean_ctor_get(v_cache_3177_, 0);
lean_inc_ref(v_inferType_3178_);
lean_dec_ref(v_cache_3177_);
v___x_3179_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3178_, v_a_3132_);
lean_dec_ref(v_inferType_3178_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_toCold_3180_; lean_object* v_cancelTk_x3f_3181_; 
lean_del_object(v___x_3134_);
v_toCold_3180_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3181_ = lean_ctor_get(v_toCold_3180_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3181_) == 1)
{
lean_object* v_val_3182_; uint8_t v___x_3183_; 
v_val_3182_ = lean_ctor_get(v_cancelTk_x3f_3181_, 0);
v___x_3183_ = l_IO_CancelToken_isSet(v_val_3182_);
if (v___x_3183_ == 0)
{
goto v___jp_3136_;
}
else
{
lean_object* v___x_3184_; lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v_a_3132_);
lean_dec(v_us_3111_);
lean_dec(v_declName_3110_);
v___x_3184_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
goto v___jp_3136_;
}
}
else
{
lean_object* v_val_3193_; lean_object* v___x_3195_; 
lean_dec(v_a_3132_);
lean_dec(v_us_3111_);
lean_dec(v_declName_3110_);
v_val_3193_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_val_3193_);
lean_dec_ref_known(v___x_3179_, 1);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v_val_3193_);
v___x_3195_ = v___x_3134_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_val_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
v___jp_3136_:
{
lean_object* v___x_3137_; 
v___x_3137_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3110_, v_us_3111_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; uint8_t v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v___x_3139_ = l_Lean_Expr_hasMVar(v_a_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3174_; 
lean_inc(v_a_3138_);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_3137_, 0);
lean_dec(v_unused_3175_);
v___x_3141_ = v___x_3137_;
v_isShared_3142_ = v_isSharedCheck_3174_;
goto v_resetjp_3140_;
}
else
{
lean_dec(v___x_3137_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3174_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v_cache_3144_; lean_object* v_mctx_3145_; lean_object* v_zetaDeltaFVarIds_3146_; lean_object* v_postponed_3147_; lean_object* v_diag_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3173_; 
v___x_3143_ = lean_st_ref_take(v_a_3060_);
v_cache_3144_ = lean_ctor_get(v___x_3143_, 1);
v_mctx_3145_ = lean_ctor_get(v___x_3143_, 0);
v_zetaDeltaFVarIds_3146_ = lean_ctor_get(v___x_3143_, 2);
v_postponed_3147_ = lean_ctor_get(v___x_3143_, 3);
v_diag_3148_ = lean_ctor_get(v___x_3143_, 4);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3150_ = v___x_3143_;
v_isShared_3151_ = v_isSharedCheck_3173_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_diag_3148_);
lean_inc(v_postponed_3147_);
lean_inc(v_zetaDeltaFVarIds_3146_);
lean_inc(v_cache_3144_);
lean_inc(v_mctx_3145_);
lean_dec(v___x_3143_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3173_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v_inferType_3152_; lean_object* v_funInfo_3153_; lean_object* v_synthInstance_3154_; lean_object* v_whnf_3155_; lean_object* v_defEqTrans_3156_; lean_object* v_defEqPerm_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3172_; 
v_inferType_3152_ = lean_ctor_get(v_cache_3144_, 0);
v_funInfo_3153_ = lean_ctor_get(v_cache_3144_, 1);
v_synthInstance_3154_ = lean_ctor_get(v_cache_3144_, 2);
v_whnf_3155_ = lean_ctor_get(v_cache_3144_, 3);
v_defEqTrans_3156_ = lean_ctor_get(v_cache_3144_, 4);
v_defEqPerm_3157_ = lean_ctor_get(v_cache_3144_, 5);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_cache_3144_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3159_ = v_cache_3144_;
v_isShared_3160_ = v_isSharedCheck_3172_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_defEqPerm_3157_);
lean_inc(v_defEqTrans_3156_);
lean_inc(v_whnf_3155_);
lean_inc(v_synthInstance_3154_);
lean_inc(v_funInfo_3153_);
lean_inc(v_inferType_3152_);
lean_dec(v_cache_3144_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3172_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3163_; 
lean_inc(v_a_3138_);
v___x_3161_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3152_, v_a_3132_, v_a_3138_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v___x_3161_);
v___x_3163_ = v___x_3159_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_funInfo_3153_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_synthInstance_3154_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_whnf_3155_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v_defEqTrans_3156_);
lean_ctor_set(v_reuseFailAlloc_3171_, 5, v_defEqPerm_3157_);
v___x_3163_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3165_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 1, v___x_3163_);
v___x_3165_ = v___x_3150_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_mctx_3145_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_zetaDeltaFVarIds_3146_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_postponed_3147_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_diag_3148_);
v___x_3165_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = lean_st_ref_put(v_a_3060_, v___x_3165_);
if (v_isShared_3142_ == 0)
{
v___x_3168_ = v___x_3141_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3138_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3132_);
return v___x_3137_;
}
}
else
{
lean_dec(v_a_3132_);
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v_us_3111_);
lean_dec(v_declName_3110_);
v_a_3198_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3131_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3131_);
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
lean_dec_ref_known(v_e_3058_, 2);
goto v___jp_3112_;
}
}
}
v___jp_3112_:
{
lean_object* v_toCold_3113_; lean_object* v_cancelTk_x3f_3114_; 
v_toCold_3113_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3114_ = lean_ctor_get(v_toCold_3113_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3114_) == 1)
{
lean_object* v_val_3115_; uint8_t v___x_3116_; 
v_val_3115_ = lean_ctor_get(v_cancelTk_x3f_3114_, 0);
v___x_3116_ = l_IO_CancelToken_isSet(v_val_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3110_, v_us_3111_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_us_3111_);
lean_dec(v_declName_3110_);
v___x_3118_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3110_, v_us_3111_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3127_;
}
}
}
case 5:
{
lean_object* v_fn_3206_; uint8_t v_cacheInferType_3207_; lean_object* v_nargs_3208_; lean_object* v___x_3209_; lean_object* v_dummy_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_fn_3206_ = lean_ctor_get(v_e_3058_, 0);
v_cacheInferType_3207_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*7 + 3);
v_nargs_3208_ = l_Lean_Expr_getAppNumArgs(v_e_3058_);
v___x_3209_ = l_Lean_Expr_getAppFn(v_fn_3206_);
v_dummy_3210_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3208_);
v___x_3211_ = lean_mk_array(v_nargs_3208_, v_dummy_3210_);
v___x_3212_ = lean_unsigned_to_nat(1u);
v___x_3213_ = lean_nat_sub(v_nargs_3208_, v___x_3212_);
lean_dec(v_nargs_3208_);
lean_inc_ref(v_e_3058_);
v___x_3214_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3058_, v___x_3211_, v___x_3213_);
if (v_cacheInferType_3207_ == 0)
{
lean_dec_ref_known(v_e_3058_, 2);
goto v___jp_3215_;
}
else
{
uint8_t v___x_3231_; 
v___x_3231_ = l_Lean_Expr_hasMVar(v_e_3058_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3298_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3298_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3298_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3277_; lean_object* v_cache_3278_; lean_object* v_inferType_3279_; lean_object* v___x_3280_; 
v___x_3277_ = lean_st_ref_get(v_a_3060_);
v_cache_3278_ = lean_ctor_get(v___x_3277_, 1);
lean_inc_ref(v_cache_3278_);
lean_dec(v___x_3277_);
v_inferType_3279_ = lean_ctor_get(v_cache_3278_, 0);
lean_inc_ref(v_inferType_3279_);
lean_dec_ref(v_cache_3278_);
v___x_3280_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3279_, v_a_3233_);
lean_dec_ref(v_inferType_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_toCold_3281_; lean_object* v_cancelTk_x3f_3282_; 
lean_del_object(v___x_3235_);
v_toCold_3281_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3282_ = lean_ctor_get(v_toCold_3281_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3282_) == 1)
{
lean_object* v_val_3283_; uint8_t v___x_3284_; 
v_val_3283_ = lean_ctor_get(v_cancelTk_x3f_3282_, 0);
v___x_3284_ = l_IO_CancelToken_isSet(v_val_3283_);
if (v___x_3284_ == 0)
{
goto v___jp_3237_;
}
else
{
lean_object* v___x_3285_; lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_a_3233_);
lean_dec_ref(v___x_3214_);
lean_dec_ref(v___x_3209_);
v___x_3285_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
goto v___jp_3237_;
}
}
else
{
lean_object* v_val_3294_; lean_object* v___x_3296_; 
lean_dec(v_a_3233_);
lean_dec_ref(v___x_3214_);
lean_dec_ref(v___x_3209_);
v_val_3294_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_val_3294_);
lean_dec_ref_known(v___x_3280_, 1);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v_val_3294_);
v___x_3296_ = v___x_3235_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_val_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
v___jp_3237_:
{
lean_object* v___x_3238_; 
v___x_3238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3209_, v___x_3214_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
lean_dec_ref(v___x_3214_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; uint8_t v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v___x_3240_ = l_Lean_Expr_hasMVar(v_a_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3275_; 
lean_inc(v_a_3239_);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3275_ == 0)
{
lean_object* v_unused_3276_; 
v_unused_3276_ = lean_ctor_get(v___x_3238_, 0);
lean_dec(v_unused_3276_);
v___x_3242_ = v___x_3238_;
v_isShared_3243_ = v_isSharedCheck_3275_;
goto v_resetjp_3241_;
}
else
{
lean_dec(v___x_3238_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3275_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v_cache_3245_; lean_object* v_mctx_3246_; lean_object* v_zetaDeltaFVarIds_3247_; lean_object* v_postponed_3248_; lean_object* v_diag_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3274_; 
v___x_3244_ = lean_st_ref_take(v_a_3060_);
v_cache_3245_ = lean_ctor_get(v___x_3244_, 1);
v_mctx_3246_ = lean_ctor_get(v___x_3244_, 0);
v_zetaDeltaFVarIds_3247_ = lean_ctor_get(v___x_3244_, 2);
v_postponed_3248_ = lean_ctor_get(v___x_3244_, 3);
v_diag_3249_ = lean_ctor_get(v___x_3244_, 4);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3251_ = v___x_3244_;
v_isShared_3252_ = v_isSharedCheck_3274_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_diag_3249_);
lean_inc(v_postponed_3248_);
lean_inc(v_zetaDeltaFVarIds_3247_);
lean_inc(v_cache_3245_);
lean_inc(v_mctx_3246_);
lean_dec(v___x_3244_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3274_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v_inferType_3253_; lean_object* v_funInfo_3254_; lean_object* v_synthInstance_3255_; lean_object* v_whnf_3256_; lean_object* v_defEqTrans_3257_; lean_object* v_defEqPerm_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3273_; 
v_inferType_3253_ = lean_ctor_get(v_cache_3245_, 0);
v_funInfo_3254_ = lean_ctor_get(v_cache_3245_, 1);
v_synthInstance_3255_ = lean_ctor_get(v_cache_3245_, 2);
v_whnf_3256_ = lean_ctor_get(v_cache_3245_, 3);
v_defEqTrans_3257_ = lean_ctor_get(v_cache_3245_, 4);
v_defEqPerm_3258_ = lean_ctor_get(v_cache_3245_, 5);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_cache_3245_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3260_ = v_cache_3245_;
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_defEqPerm_3258_);
lean_inc(v_defEqTrans_3257_);
lean_inc(v_whnf_3256_);
lean_inc(v_synthInstance_3255_);
lean_inc(v_funInfo_3254_);
lean_inc(v_inferType_3253_);
lean_dec(v_cache_3245_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3273_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_inc(v_a_3239_);
v___x_3262_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3253_, v_a_3233_, v_a_3239_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3262_);
v___x_3264_ = v___x_3260_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_funInfo_3254_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_synthInstance_3255_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_whnf_3256_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_defEqTrans_3257_);
lean_ctor_set(v_reuseFailAlloc_3272_, 5, v_defEqPerm_3258_);
v___x_3264_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3266_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v___x_3264_);
v___x_3266_ = v___x_3251_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_mctx_3246_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_zetaDeltaFVarIds_3247_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_postponed_3248_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v_diag_3249_);
v___x_3266_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3267_ = lean_st_ref_put(v_a_3060_, v___x_3266_);
if (v_isShared_3243_ == 0)
{
v___x_3269_ = v___x_3242_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3239_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3233_);
return v___x_3238_;
}
}
else
{
lean_dec(v_a_3233_);
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec_ref(v___x_3214_);
lean_dec_ref(v___x_3209_);
v_a_3299_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3232_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3232_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3058_, 2);
goto v___jp_3215_;
}
}
v___jp_3215_:
{
lean_object* v_toCold_3216_; lean_object* v_cancelTk_x3f_3217_; 
v_toCold_3216_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3217_ = lean_ctor_get(v_toCold_3216_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3217_) == 1)
{
lean_object* v_val_3218_; uint8_t v___x_3219_; 
v_val_3218_ = lean_ctor_get(v_cancelTk_x3f_3217_, 0);
v___x_3219_ = l_IO_CancelToken_isSet(v_val_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
v___x_3220_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3209_, v___x_3214_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
lean_dec_ref(v___x_3214_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v___x_3214_);
lean_dec_ref(v___x_3209_);
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
v___x_3230_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3209_, v___x_3214_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
lean_dec_ref(v___x_3214_);
return v___x_3230_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3307_; 
v_cacheInferType_3307_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3307_ == 0)
{
goto v___jp_3080_;
}
else
{
uint8_t v___x_3308_; 
v___x_3308_ = l_Lean_Expr_hasMVar(v_e_3058_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; 
lean_inc_ref(v_e_3058_);
v___x_3309_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3375_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3375_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3375_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3354_; lean_object* v_cache_3355_; lean_object* v_inferType_3356_; lean_object* v___x_3357_; 
v___x_3354_ = lean_st_ref_get(v_a_3060_);
v_cache_3355_ = lean_ctor_get(v___x_3354_, 1);
lean_inc_ref(v_cache_3355_);
lean_dec(v___x_3354_);
v_inferType_3356_ = lean_ctor_get(v_cache_3355_, 0);
lean_inc_ref(v_inferType_3356_);
lean_dec_ref(v_cache_3355_);
v___x_3357_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3356_, v_a_3310_);
lean_dec_ref(v_inferType_3356_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_toCold_3358_; lean_object* v_cancelTk_x3f_3359_; 
lean_del_object(v___x_3312_);
v_toCold_3358_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3359_ = lean_ctor_get(v_toCold_3358_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3359_) == 1)
{
lean_object* v_val_3360_; uint8_t v___x_3361_; 
v_val_3360_ = lean_ctor_get(v_cancelTk_x3f_3359_, 0);
v___x_3361_ = l_IO_CancelToken_isSet(v_val_3360_);
if (v___x_3361_ == 0)
{
goto v___jp_3314_;
}
else
{
lean_object* v___x_3362_; lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v_a_3310_);
lean_dec_ref_known(v_e_3058_, 3);
v___x_3362_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
goto v___jp_3314_;
}
}
else
{
lean_object* v_val_3371_; lean_object* v___x_3373_; 
lean_dec(v_a_3310_);
lean_dec_ref_known(v_e_3058_, 3);
v_val_3371_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_val_3371_);
lean_dec_ref_known(v___x_3357_, 1);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_val_3371_);
v___x_3373_ = v___x_3312_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_val_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
v___jp_3314_:
{
lean_object* v___x_3315_; 
v___x_3315_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; uint8_t v___x_3317_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v___x_3317_ = l_Lean_Expr_hasMVar(v_a_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3352_; 
lean_inc(v_a_3316_);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; 
v_unused_3353_ = lean_ctor_get(v___x_3315_, 0);
lean_dec(v_unused_3353_);
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3352_;
goto v_resetjp_3318_;
}
else
{
lean_dec(v___x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3352_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v_cache_3322_; lean_object* v_mctx_3323_; lean_object* v_zetaDeltaFVarIds_3324_; lean_object* v_postponed_3325_; lean_object* v_diag_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3351_; 
v___x_3321_ = lean_st_ref_take(v_a_3060_);
v_cache_3322_ = lean_ctor_get(v___x_3321_, 1);
v_mctx_3323_ = lean_ctor_get(v___x_3321_, 0);
v_zetaDeltaFVarIds_3324_ = lean_ctor_get(v___x_3321_, 2);
v_postponed_3325_ = lean_ctor_get(v___x_3321_, 3);
v_diag_3326_ = lean_ctor_get(v___x_3321_, 4);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3328_ = v___x_3321_;
v_isShared_3329_ = v_isSharedCheck_3351_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_diag_3326_);
lean_inc(v_postponed_3325_);
lean_inc(v_zetaDeltaFVarIds_3324_);
lean_inc(v_cache_3322_);
lean_inc(v_mctx_3323_);
lean_dec(v___x_3321_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3351_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_inferType_3330_; lean_object* v_funInfo_3331_; lean_object* v_synthInstance_3332_; lean_object* v_whnf_3333_; lean_object* v_defEqTrans_3334_; lean_object* v_defEqPerm_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3350_; 
v_inferType_3330_ = lean_ctor_get(v_cache_3322_, 0);
v_funInfo_3331_ = lean_ctor_get(v_cache_3322_, 1);
v_synthInstance_3332_ = lean_ctor_get(v_cache_3322_, 2);
v_whnf_3333_ = lean_ctor_get(v_cache_3322_, 3);
v_defEqTrans_3334_ = lean_ctor_get(v_cache_3322_, 4);
v_defEqPerm_3335_ = lean_ctor_get(v_cache_3322_, 5);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_cache_3322_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3337_ = v_cache_3322_;
v_isShared_3338_ = v_isSharedCheck_3350_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_defEqPerm_3335_);
lean_inc(v_defEqTrans_3334_);
lean_inc(v_whnf_3333_);
lean_inc(v_synthInstance_3332_);
lean_inc(v_funInfo_3331_);
lean_inc(v_inferType_3330_);
lean_dec(v_cache_3322_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3350_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
lean_inc(v_a_3316_);
v___x_3339_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3330_, v_a_3310_, v_a_3316_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3339_);
v___x_3341_ = v___x_3337_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_funInfo_3331_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_synthInstance_3332_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_whnf_3333_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_defEqTrans_3334_);
lean_ctor_set(v_reuseFailAlloc_3349_, 5, v_defEqPerm_3335_);
v___x_3341_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3343_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 1, v___x_3341_);
v___x_3343_ = v___x_3328_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_mctx_3323_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_zetaDeltaFVarIds_3324_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_postponed_3325_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v_diag_3326_);
v___x_3343_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3344_ = lean_st_ref_put(v_a_3060_, v___x_3343_);
if (v_isShared_3320_ == 0)
{
v___x_3346_ = v___x_3319_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3316_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3310_);
return v___x_3315_;
}
}
else
{
lean_dec(v_a_3310_);
return v___x_3315_;
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref_known(v_e_3058_, 3);
v_a_3376_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3309_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3309_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
goto v___jp_3080_;
}
}
}
case 9:
{
lean_object* v_a_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_a_3384_ = lean_ctor_get(v_e_3058_, 0);
lean_inc_ref(v_a_3384_);
lean_dec_ref_known(v_e_3058_, 1);
v___x_3385_ = l_Lean_Literal_type(v_a_3384_);
lean_dec_ref(v_a_3384_);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
case 10:
{
lean_object* v_expr_3387_; 
v_expr_3387_ = lean_ctor_get(v_e_3058_, 1);
lean_inc_ref(v_expr_3387_);
lean_dec_ref_known(v_e_3058_, 2);
v_e_3058_ = v_expr_3387_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3389_; lean_object* v_idx_3390_; lean_object* v_struct_3391_; uint8_t v_cacheInferType_3408_; 
v_typeName_3389_ = lean_ctor_get(v_e_3058_, 0);
lean_inc(v_typeName_3389_);
v_idx_3390_ = lean_ctor_get(v_e_3058_, 1);
lean_inc(v_idx_3390_);
v_struct_3391_ = lean_ctor_get(v_e_3058_, 2);
lean_inc_ref(v_struct_3391_);
v_cacheInferType_3408_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3408_ == 0)
{
lean_dec_ref_known(v_e_3058_, 3);
goto v___jp_3392_;
}
else
{
uint8_t v___x_3409_; 
v___x_3409_ = l_Lean_Expr_hasMVar(v_e_3058_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3476_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3476_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3476_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3455_; lean_object* v_cache_3456_; lean_object* v_inferType_3457_; lean_object* v___x_3458_; 
v___x_3455_ = lean_st_ref_get(v_a_3060_);
v_cache_3456_ = lean_ctor_get(v___x_3455_, 1);
lean_inc_ref(v_cache_3456_);
lean_dec(v___x_3455_);
v_inferType_3457_ = lean_ctor_get(v_cache_3456_, 0);
lean_inc_ref(v_inferType_3457_);
lean_dec_ref(v_cache_3456_);
v___x_3458_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3457_, v_a_3411_);
lean_dec_ref(v_inferType_3457_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_toCold_3459_; lean_object* v_cancelTk_x3f_3460_; 
lean_del_object(v___x_3413_);
v_toCold_3459_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3460_ = lean_ctor_get(v_toCold_3459_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3460_) == 1)
{
lean_object* v_val_3461_; uint8_t v___x_3462_; 
v_val_3461_ = lean_ctor_get(v_cancelTk_x3f_3460_, 0);
v___x_3462_ = l_IO_CancelToken_isSet(v_val_3461_);
if (v___x_3462_ == 0)
{
goto v___jp_3415_;
}
else
{
lean_object* v___x_3463_; lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v_a_3411_);
lean_dec_ref(v_struct_3391_);
lean_dec(v_idx_3390_);
lean_dec(v_typeName_3389_);
v___x_3463_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
goto v___jp_3415_;
}
}
else
{
lean_object* v_val_3472_; lean_object* v___x_3474_; 
lean_dec(v_a_3411_);
lean_dec_ref(v_struct_3391_);
lean_dec(v_idx_3390_);
lean_dec(v_typeName_3389_);
v_val_3472_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_val_3472_);
lean_dec_ref_known(v___x_3458_, 1);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v_val_3472_);
v___x_3474_ = v___x_3413_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_val_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
v___jp_3415_:
{
lean_object* v___x_3416_; 
v___x_3416_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3389_, v_idx_3390_, v_struct_3391_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; uint8_t v___x_3418_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v___x_3418_ = l_Lean_Expr_hasMVar(v_a_3417_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3453_; 
lean_inc(v_a_3417_);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3453_ == 0)
{
lean_object* v_unused_3454_; 
v_unused_3454_ = lean_ctor_get(v___x_3416_, 0);
lean_dec(v_unused_3454_);
v___x_3420_ = v___x_3416_;
v_isShared_3421_ = v_isSharedCheck_3453_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v___x_3416_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3453_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v_cache_3423_; lean_object* v_mctx_3424_; lean_object* v_zetaDeltaFVarIds_3425_; lean_object* v_postponed_3426_; lean_object* v_diag_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3452_; 
v___x_3422_ = lean_st_ref_take(v_a_3060_);
v_cache_3423_ = lean_ctor_get(v___x_3422_, 1);
v_mctx_3424_ = lean_ctor_get(v___x_3422_, 0);
v_zetaDeltaFVarIds_3425_ = lean_ctor_get(v___x_3422_, 2);
v_postponed_3426_ = lean_ctor_get(v___x_3422_, 3);
v_diag_3427_ = lean_ctor_get(v___x_3422_, 4);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3429_ = v___x_3422_;
v_isShared_3430_ = v_isSharedCheck_3452_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_diag_3427_);
lean_inc(v_postponed_3426_);
lean_inc(v_zetaDeltaFVarIds_3425_);
lean_inc(v_cache_3423_);
lean_inc(v_mctx_3424_);
lean_dec(v___x_3422_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3452_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v_inferType_3431_; lean_object* v_funInfo_3432_; lean_object* v_synthInstance_3433_; lean_object* v_whnf_3434_; lean_object* v_defEqTrans_3435_; lean_object* v_defEqPerm_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3451_; 
v_inferType_3431_ = lean_ctor_get(v_cache_3423_, 0);
v_funInfo_3432_ = lean_ctor_get(v_cache_3423_, 1);
v_synthInstance_3433_ = lean_ctor_get(v_cache_3423_, 2);
v_whnf_3434_ = lean_ctor_get(v_cache_3423_, 3);
v_defEqTrans_3435_ = lean_ctor_get(v_cache_3423_, 4);
v_defEqPerm_3436_ = lean_ctor_get(v_cache_3423_, 5);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_cache_3423_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3438_ = v_cache_3423_;
v_isShared_3439_ = v_isSharedCheck_3451_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_defEqPerm_3436_);
lean_inc(v_defEqTrans_3435_);
lean_inc(v_whnf_3434_);
lean_inc(v_synthInstance_3433_);
lean_inc(v_funInfo_3432_);
lean_inc(v_inferType_3431_);
lean_dec(v_cache_3423_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3451_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_inc(v_a_3417_);
v___x_3440_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3431_, v_a_3411_, v_a_3417_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_funInfo_3432_);
lean_ctor_set(v_reuseFailAlloc_3450_, 2, v_synthInstance_3433_);
lean_ctor_set(v_reuseFailAlloc_3450_, 3, v_whnf_3434_);
lean_ctor_set(v_reuseFailAlloc_3450_, 4, v_defEqTrans_3435_);
lean_ctor_set(v_reuseFailAlloc_3450_, 5, v_defEqPerm_3436_);
v___x_3442_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3442_);
v___x_3444_ = v___x_3429_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_mctx_3424_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_zetaDeltaFVarIds_3425_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_postponed_3426_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_diag_3427_);
v___x_3444_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = lean_st_ref_put(v_a_3060_, v___x_3444_);
if (v_isShared_3421_ == 0)
{
v___x_3447_ = v___x_3420_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3417_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3411_);
return v___x_3416_;
}
}
else
{
lean_dec(v_a_3411_);
return v___x_3416_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v_struct_3391_);
lean_dec(v_idx_3390_);
lean_dec(v_typeName_3389_);
v_a_3477_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3410_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3410_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3058_, 3);
goto v___jp_3392_;
}
}
v___jp_3392_:
{
lean_object* v_toCold_3393_; lean_object* v_cancelTk_x3f_3394_; 
v_toCold_3393_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3394_ = lean_ctor_get(v_toCold_3393_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3394_) == 1)
{
lean_object* v_val_3395_; uint8_t v___x_3396_; 
v_val_3395_ = lean_ctor_get(v_cancelTk_x3f_3394_, 0);
v___x_3396_ = l_IO_CancelToken_isSet(v_val_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3389_, v_idx_3390_, v_struct_3391_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3397_;
}
else
{
lean_object* v___x_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v_struct_3391_);
lean_dec(v_idx_3390_);
lean_dec(v_typeName_3389_);
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
lean_object* v___x_3407_; 
v___x_3407_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3389_, v_idx_3390_, v_struct_3391_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3407_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3485_; 
v_cacheInferType_3485_ = lean_ctor_get_uint8(v_a_3059_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3485_ == 0)
{
goto v___jp_3064_;
}
else
{
uint8_t v___x_3486_; 
v___x_3486_ = l_Lean_Expr_hasMVar(v_e_3058_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
lean_inc_ref(v_e_3058_);
v___x_3487_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3058_, v_a_3059_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3553_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3553_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3553_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3532_; lean_object* v_cache_3533_; lean_object* v_inferType_3534_; lean_object* v___x_3535_; 
v___x_3532_ = lean_st_ref_get(v_a_3060_);
v_cache_3533_ = lean_ctor_get(v___x_3532_, 1);
lean_inc_ref(v_cache_3533_);
lean_dec(v___x_3532_);
v_inferType_3534_ = lean_ctor_get(v_cache_3533_, 0);
lean_inc_ref(v_inferType_3534_);
lean_dec_ref(v_cache_3533_);
v___x_3535_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3534_, v_a_3488_);
lean_dec_ref(v_inferType_3534_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_toCold_3536_; lean_object* v_cancelTk_x3f_3537_; 
lean_del_object(v___x_3490_);
v_toCold_3536_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3537_ = lean_ctor_get(v_toCold_3536_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3537_) == 1)
{
lean_object* v_val_3538_; uint8_t v___x_3539_; 
v_val_3538_ = lean_ctor_get(v_cancelTk_x3f_3537_, 0);
v___x_3539_ = l_IO_CancelToken_isSet(v_val_3538_);
if (v___x_3539_ == 0)
{
goto v___jp_3492_;
}
else
{
lean_object* v___x_3540_; lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_a_3488_);
lean_dec_ref(v_e_3058_);
v___x_3540_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3540_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3540_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
goto v___jp_3492_;
}
}
else
{
lean_object* v_val_3549_; lean_object* v___x_3551_; 
lean_dec(v_a_3488_);
lean_dec_ref(v_e_3058_);
v_val_3549_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_val_3549_);
lean_dec_ref_known(v___x_3535_, 1);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v_val_3549_);
v___x_3551_ = v___x_3490_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_val_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
v___jp_3492_:
{
lean_object* v___x_3493_; 
v___x_3493_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; uint8_t v___x_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v___x_3495_ = l_Lean_Expr_hasMVar(v_a_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3530_; 
lean_inc(v_a_3494_);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v___x_3493_, 0);
lean_dec(v_unused_3531_);
v___x_3497_ = v___x_3493_;
v_isShared_3498_ = v_isSharedCheck_3530_;
goto v_resetjp_3496_;
}
else
{
lean_dec(v___x_3493_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3530_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; lean_object* v_cache_3500_; lean_object* v_mctx_3501_; lean_object* v_zetaDeltaFVarIds_3502_; lean_object* v_postponed_3503_; lean_object* v_diag_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3529_; 
v___x_3499_ = lean_st_ref_take(v_a_3060_);
v_cache_3500_ = lean_ctor_get(v___x_3499_, 1);
v_mctx_3501_ = lean_ctor_get(v___x_3499_, 0);
v_zetaDeltaFVarIds_3502_ = lean_ctor_get(v___x_3499_, 2);
v_postponed_3503_ = lean_ctor_get(v___x_3499_, 3);
v_diag_3504_ = lean_ctor_get(v___x_3499_, 4);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3506_ = v___x_3499_;
v_isShared_3507_ = v_isSharedCheck_3529_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_diag_3504_);
lean_inc(v_postponed_3503_);
lean_inc(v_zetaDeltaFVarIds_3502_);
lean_inc(v_cache_3500_);
lean_inc(v_mctx_3501_);
lean_dec(v___x_3499_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3529_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_inferType_3508_; lean_object* v_funInfo_3509_; lean_object* v_synthInstance_3510_; lean_object* v_whnf_3511_; lean_object* v_defEqTrans_3512_; lean_object* v_defEqPerm_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3528_; 
v_inferType_3508_ = lean_ctor_get(v_cache_3500_, 0);
v_funInfo_3509_ = lean_ctor_get(v_cache_3500_, 1);
v_synthInstance_3510_ = lean_ctor_get(v_cache_3500_, 2);
v_whnf_3511_ = lean_ctor_get(v_cache_3500_, 3);
v_defEqTrans_3512_ = lean_ctor_get(v_cache_3500_, 4);
v_defEqPerm_3513_ = lean_ctor_get(v_cache_3500_, 5);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_cache_3500_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3515_ = v_cache_3500_;
v_isShared_3516_ = v_isSharedCheck_3528_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_defEqPerm_3513_);
lean_inc(v_defEqTrans_3512_);
lean_inc(v_whnf_3511_);
lean_inc(v_synthInstance_3510_);
lean_inc(v_funInfo_3509_);
lean_inc(v_inferType_3508_);
lean_dec(v_cache_3500_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3528_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_inc(v_a_3494_);
v___x_3517_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3508_, v_a_3488_, v_a_3494_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3517_);
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_funInfo_3509_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_synthInstance_3510_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_whnf_3511_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_defEqTrans_3512_);
lean_ctor_set(v_reuseFailAlloc_3527_, 5, v_defEqPerm_3513_);
v___x_3519_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v___x_3519_);
v___x_3521_ = v___x_3506_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_mctx_3501_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_zetaDeltaFVarIds_3502_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_postponed_3503_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_diag_3504_);
v___x_3521_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3522_ = lean_st_ref_put(v_a_3060_, v___x_3521_);
if (v_isShared_3498_ == 0)
{
v___x_3524_ = v___x_3497_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3494_);
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
lean_dec(v_a_3488_);
return v___x_3493_;
}
}
else
{
lean_dec(v_a_3488_);
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec_ref(v_e_3058_);
v_a_3554_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3487_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3487_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
else
{
goto v___jp_3064_;
}
}
}
}
v___jp_3064_:
{
lean_object* v_toCold_3065_; lean_object* v_cancelTk_x3f_3066_; 
v_toCold_3065_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3066_ = lean_ctor_get(v_toCold_3065_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3066_) == 1)
{
lean_object* v_val_3067_; uint8_t v___x_3068_; 
v_val_3067_ = lean_ctor_get(v_cancelTk_x3f_3066_, 0);
v___x_3068_ = l_IO_CancelToken_isSet(v_val_3067_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3069_;
}
else
{
lean_object* v___x_3070_; lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_e_3058_);
v___x_3070_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v___x_3079_; 
v___x_3079_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3079_;
}
}
v___jp_3080_:
{
lean_object* v_toCold_3081_; lean_object* v_cancelTk_x3f_3082_; 
v_toCold_3081_ = lean_ctor_get(v_a_3061_, 0);
v_cancelTk_x3f_3082_ = lean_ctor_get(v_toCold_3081_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3082_) == 1)
{
lean_object* v_val_3083_; uint8_t v___x_3084_; 
v_val_3083_ = lean_ctor_get(v_cancelTk_x3f_3082_, 0);
v___x_3084_ = l_IO_CancelToken_isSet(v_val_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3085_;
}
else
{
lean_object* v___x_3086_; lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v_e_3058_);
v___x_3086_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
return v___x_3095_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3569_, lean_object* v_x_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3570_, v_x_3571_, v_x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3575_, v_x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3578_, lean_object* v_x_3579_, lean_object* v_x_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3578_, v_x_3579_, v_x_3580_);
lean_dec_ref(v_x_3580_);
lean_dec_ref(v_x_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3582_, lean_object* v_x_3583_, size_t v_x_3584_, size_t v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3583_, v_x_3584_, v_x_3585_, v_x_3586_, v_x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_){
_start:
{
size_t v_x_3637__boxed_3595_; size_t v_x_3638__boxed_3596_; lean_object* v_res_3597_; 
v_x_3637__boxed_3595_ = lean_unbox_usize(v_x_3591_);
lean_dec(v_x_3591_);
v_x_3638__boxed_3596_ = lean_unbox_usize(v_x_3592_);
lean_dec(v_x_3592_);
v_res_3597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3589_, v_x_3590_, v_x_3637__boxed_3595_, v_x_3638__boxed_3596_, v_x_3593_, v_x_3594_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3598_, lean_object* v_x_3599_, size_t v_x_3600_, lean_object* v_x_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3599_, v_x_3600_, v_x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3603_, lean_object* v_x_3604_, lean_object* v_x_3605_, lean_object* v_x_3606_){
_start:
{
size_t v_x_3654__boxed_3607_; lean_object* v_res_3608_; 
v_x_3654__boxed_3607_ = lean_unbox_usize(v_x_3605_);
lean_dec(v_x_3605_);
v_res_3608_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3603_, v_x_3604_, v_x_3654__boxed_3607_, v_x_3606_);
lean_dec_ref(v_x_3606_);
lean_dec_ref(v_x_3604_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3609_, lean_object* v_n_3610_, lean_object* v_k_3611_, lean_object* v_v_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3610_, v_k_3611_, v_v_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3614_, size_t v_depth_3615_, lean_object* v_keys_3616_, lean_object* v_vals_3617_, lean_object* v_heq_3618_, lean_object* v_i_3619_, lean_object* v_entries_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3615_, v_keys_3616_, v_vals_3617_, v_i_3619_, v_entries_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3622_, lean_object* v_depth_3623_, lean_object* v_keys_3624_, lean_object* v_vals_3625_, lean_object* v_heq_3626_, lean_object* v_i_3627_, lean_object* v_entries_3628_){
_start:
{
size_t v_depth_boxed_3629_; lean_object* v_res_3630_; 
v_depth_boxed_3629_ = lean_unbox_usize(v_depth_3623_);
lean_dec(v_depth_3623_);
v_res_3630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3622_, v_depth_boxed_3629_, v_keys_3624_, v_vals_3625_, v_heq_3626_, v_i_3627_, v_entries_3628_);
lean_dec_ref(v_vals_3625_);
lean_dec_ref(v_keys_3624_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3631_, lean_object* v_keys_3632_, lean_object* v_vals_3633_, lean_object* v_heq_3634_, lean_object* v_i_3635_, lean_object* v_k_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3632_, v_vals_3633_, v_i_3635_, v_k_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3638_, lean_object* v_keys_3639_, lean_object* v_vals_3640_, lean_object* v_heq_3641_, lean_object* v_i_3642_, lean_object* v_k_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3638_, v_keys_3639_, v_vals_3640_, v_heq_3641_, v_i_3642_, v_k_3643_);
lean_dec_ref(v_k_3643_);
lean_dec_ref(v_vals_3640_);
lean_dec_ref(v_keys_3639_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3645_, lean_object* v_x_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3646_, v_x_3647_, v_x_3648_, v_x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = l_Lean_maxRecDepthErrorMessage;
v___x_3657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3659_ = l_Lean_MessageData_ofFormat(v___x_3658_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3661_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3662_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
lean_ctor_set(v___x_3662_, 1, v___x_3660_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3663_){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v_ref_3663_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3671_, lean_object* v_ref_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3672_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3679_, lean_object* v_ref_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3679_, v_ref_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0(lean_object* v_e_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v___x_3739_; uint8_t v_beta_3740_; 
v___x_3739_ = l_Lean_Meta_Context_config(v___y_3688_);
v_beta_3740_ = lean_ctor_get_uint8(v___x_3739_, 13);
if (v_beta_3740_ == 0)
{
lean_dec_ref(v___x_3739_);
goto v___jp_3693_;
}
else
{
uint8_t v_iota_3741_; 
v_iota_3741_ = lean_ctor_get_uint8(v___x_3739_, 12);
if (v_iota_3741_ == 0)
{
lean_dec_ref(v___x_3739_);
goto v___jp_3693_;
}
else
{
uint8_t v_zeta_3742_; 
v_zeta_3742_ = lean_ctor_get_uint8(v___x_3739_, 15);
if (v_zeta_3742_ == 0)
{
lean_dec_ref(v___x_3739_);
goto v___jp_3693_;
}
else
{
uint8_t v_zetaHave_3743_; 
v_zetaHave_3743_ = lean_ctor_get_uint8(v___x_3739_, 18);
if (v_zetaHave_3743_ == 0)
{
lean_dec_ref(v___x_3739_);
goto v___jp_3693_;
}
else
{
uint8_t v_zetaDelta_3744_; 
v_zetaDelta_3744_ = lean_ctor_get_uint8(v___x_3739_, 16);
if (v_zetaDelta_3744_ == 0)
{
lean_dec_ref(v___x_3739_);
goto v___jp_3693_;
}
else
{
uint8_t v_etaStruct_3745_; uint8_t v_proj_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v_etaStruct_3745_ = lean_ctor_get_uint8(v___x_3739_, 10);
v_proj_3746_ = lean_ctor_get_uint8(v___x_3739_, 14);
lean_dec_ref(v___x_3739_);
v___x_3747_ = lean_box(v_proj_3746_);
v___x_3748_ = lean_obj_tag_nat(v___x_3747_);
lean_dec(v___x_3747_);
v___x_3749_ = lean_unsigned_to_nat(2u);
v___x_3750_ = lean_nat_dec_eq(v___x_3748_, v___x_3749_);
if (v___x_3750_ == 0)
{
goto v___jp_3693_;
}
else
{
uint8_t v___x_3751_; uint8_t v___x_3752_; 
v___x_3751_ = 0;
v___x_3752_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3745_, v___x_3751_);
if (v___x_3752_ == 0)
{
goto v___jp_3693_;
}
else
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec_ref(v___y_3688_);
return v___x_3753_;
}
}
}
}
}
}
}
v___jp_3693_:
{
lean_object* v___x_3694_; uint8_t v_foApprox_3695_; uint8_t v_ctxApprox_3696_; uint8_t v_quasiPatternApprox_3697_; uint8_t v_constApprox_3698_; uint8_t v_isDefEqStuckEx_3699_; uint8_t v_unificationHints_3700_; uint8_t v_proofIrrelevance_3701_; uint8_t v_assignSyntheticOpaque_3702_; uint8_t v_offsetCnstrs_3703_; uint8_t v_transparency_3704_; uint8_t v_univApprox_3705_; uint8_t v_zetaUnused_3706_; uint8_t v_canUnfoldPredicateConfig_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3738_; 
v___x_3694_ = l_Lean_Meta_Context_config(v___y_3688_);
v_foApprox_3695_ = lean_ctor_get_uint8(v___x_3694_, 0);
v_ctxApprox_3696_ = lean_ctor_get_uint8(v___x_3694_, 1);
v_quasiPatternApprox_3697_ = lean_ctor_get_uint8(v___x_3694_, 2);
v_constApprox_3698_ = lean_ctor_get_uint8(v___x_3694_, 3);
v_isDefEqStuckEx_3699_ = lean_ctor_get_uint8(v___x_3694_, 4);
v_unificationHints_3700_ = lean_ctor_get_uint8(v___x_3694_, 5);
v_proofIrrelevance_3701_ = lean_ctor_get_uint8(v___x_3694_, 6);
v_assignSyntheticOpaque_3702_ = lean_ctor_get_uint8(v___x_3694_, 7);
v_offsetCnstrs_3703_ = lean_ctor_get_uint8(v___x_3694_, 8);
v_transparency_3704_ = lean_ctor_get_uint8(v___x_3694_, 9);
v_univApprox_3705_ = lean_ctor_get_uint8(v___x_3694_, 11);
v_zetaUnused_3706_ = lean_ctor_get_uint8(v___x_3694_, 17);
v_canUnfoldPredicateConfig_3707_ = lean_ctor_get_uint8(v___x_3694_, 19);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3709_ = v___x_3694_;
v_isShared_3710_ = v_isSharedCheck_3738_;
goto v_resetjp_3708_;
}
else
{
lean_dec(v___x_3694_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3738_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
uint8_t v___x_3711_; uint8_t v___x_3712_; uint8_t v___x_3713_; lean_object* v___x_3715_; 
v___x_3711_ = 1;
v___x_3712_ = 0;
v___x_3713_ = 2;
if (v_isShared_3710_ == 0)
{
v___x_3715_ = v___x_3709_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 0, v_foApprox_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 1, v_ctxApprox_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 2, v_quasiPatternApprox_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 3, v_constApprox_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 4, v_isDefEqStuckEx_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 5, v_unificationHints_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 6, v_proofIrrelevance_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 7, v_assignSyntheticOpaque_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 8, v_offsetCnstrs_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 9, v_transparency_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 11, v_univApprox_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 17, v_zetaUnused_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3737_, 19, v_canUnfoldPredicateConfig_3707_);
v___x_3715_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
uint8_t v_trackZetaDelta_3716_; lean_object* v_zetaDeltaSet_3717_; lean_object* v_lctx_3718_; lean_object* v_localInstances_3719_; lean_object* v_defEqCtx_x3f_3720_; lean_object* v_synthPendingDepth_3721_; lean_object* v_customCanUnfoldPredicate_x3f_3722_; uint8_t v_univApprox_3723_; uint8_t v_inTypeClassResolution_3724_; uint8_t v_cacheInferType_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3735_; 
lean_ctor_set_uint8(v___x_3715_, 10, v___x_3712_);
lean_ctor_set_uint8(v___x_3715_, 12, v___x_3711_);
lean_ctor_set_uint8(v___x_3715_, 13, v___x_3711_);
lean_ctor_set_uint8(v___x_3715_, 14, v___x_3713_);
lean_ctor_set_uint8(v___x_3715_, 15, v___x_3711_);
lean_ctor_set_uint8(v___x_3715_, 16, v___x_3711_);
lean_ctor_set_uint8(v___x_3715_, 18, v___x_3711_);
v_trackZetaDelta_3716_ = lean_ctor_get_uint8(v___y_3688_, sizeof(void*)*7);
v_zetaDeltaSet_3717_ = lean_ctor_get(v___y_3688_, 1);
v_lctx_3718_ = lean_ctor_get(v___y_3688_, 2);
v_localInstances_3719_ = lean_ctor_get(v___y_3688_, 3);
v_defEqCtx_x3f_3720_ = lean_ctor_get(v___y_3688_, 4);
v_synthPendingDepth_3721_ = lean_ctor_get(v___y_3688_, 5);
v_customCanUnfoldPredicate_x3f_3722_ = lean_ctor_get(v___y_3688_, 6);
v_univApprox_3723_ = lean_ctor_get_uint8(v___y_3688_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3724_ = lean_ctor_get_uint8(v___y_3688_, sizeof(void*)*7 + 2);
v_cacheInferType_3725_ = lean_ctor_get_uint8(v___y_3688_, sizeof(void*)*7 + 3);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___y_3688_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v___y_3688_, 0);
lean_dec(v_unused_3736_);
v___x_3727_ = v___y_3688_;
v_isShared_3728_ = v_isSharedCheck_3735_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3722_);
lean_inc(v_synthPendingDepth_3721_);
lean_inc(v_defEqCtx_x3f_3720_);
lean_inc(v_localInstances_3719_);
lean_inc(v_lctx_3718_);
lean_inc(v_zetaDeltaSet_3717_);
lean_dec(v___y_3688_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3735_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
uint64_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3732_; 
v___x_3729_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3715_);
v___x_3730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3730_, 0, v___x_3715_);
lean_ctor_set_uint64(v___x_3730_, sizeof(void*)*1, v___x_3729_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3730_);
v___x_3732_ = v___x_3727_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3730_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_zetaDeltaSet_3717_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_lctx_3718_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_localInstances_3719_);
lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_defEqCtx_x3f_3720_);
lean_ctor_set(v_reuseFailAlloc_3734_, 5, v_synthPendingDepth_3721_);
lean_ctor_set(v_reuseFailAlloc_3734_, 6, v_customCanUnfoldPredicate_x3f_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3734_, sizeof(void*)*7, v_trackZetaDelta_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3734_, sizeof(void*)*7 + 1, v_univApprox_3723_);
lean_ctor_set_uint8(v_reuseFailAlloc_3734_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3734_, sizeof(void*)*7 + 3, v_cacheInferType_3725_);
v___x_3732_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_object* v___x_3733_; 
v___x_3733_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3687_, v___x_3732_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec_ref(v___x_3732_);
return v___x_3733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___lam__0___boxed(lean_object* v_e_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v___y_3768_; lean_object* v_toCold_3785_; lean_object* v_currRecDepth_3786_; lean_object* v_ref_3787_; uint16_t v_optionFlags_3788_; uint8_t v_suppressElabErrors_3789_; uint8_t v_isRecordingDeps_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3830_; 
v_toCold_3785_ = lean_ctor_get(v_a_3764_, 0);
v_currRecDepth_3786_ = lean_ctor_get(v_a_3764_, 1);
v_ref_3787_ = lean_ctor_get(v_a_3764_, 2);
v_optionFlags_3788_ = lean_ctor_get_uint16(v_a_3764_, sizeof(void*)*3);
v_suppressElabErrors_3789_ = lean_ctor_get_uint8(v_a_3764_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3790_ = lean_ctor_get_uint8(v_a_3764_, sizeof(void*)*3 + 3);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_a_3764_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3792_ = v_a_3764_;
v_isShared_3793_ = v_isSharedCheck_3830_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_ref_3787_);
lean_inc(v_currRecDepth_3786_);
lean_inc(v_toCold_3785_);
lean_dec(v_a_3764_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3830_;
goto v_resetjp_3791_;
}
v___jp_3767_:
{
if (lean_obj_tag(v___y_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
v_a_3769_ = lean_ctor_get(v___y_3768_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___y_3768_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___y_3768_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___y_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
v_a_3777_ = lean_ctor_get(v___y_3768_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___y_3768_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___y_3768_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___y_3768_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
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
v_resetjp_3791_:
{
lean_object* v_maxRecDepth_3794_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_maxRecDepth_3794_ = lean_ctor_get(v_toCold_3785_, 3);
v___x_3826_ = lean_unsigned_to_nat(0u);
v___x_3827_ = lean_nat_dec_eq(v_maxRecDepth_3794_, v___x_3826_);
if (v___x_3827_ == 0)
{
uint8_t v___x_3828_; 
v___x_3828_ = lean_nat_dec_eq(v_currRecDepth_3786_, v_maxRecDepth_3794_);
if (v___x_3828_ == 0)
{
goto v___jp_3795_;
}
else
{
lean_object* v___x_3829_; 
lean_del_object(v___x_3792_);
lean_dec(v_currRecDepth_3786_);
lean_dec_ref(v_toCold_3785_);
lean_dec(v_a_3765_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec_ref(v_e_3761_);
v___x_3829_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3787_);
return v___x_3829_;
}
}
else
{
goto v___jp_3795_;
}
v___jp_3795_:
{
lean_object* v___x_3796_; uint8_t v_transparency_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3796_ = l_Lean_Meta_Context_config(v_a_3762_);
v_transparency_3797_ = lean_ctor_get_uint8(v___x_3796_, 9);
lean_dec_ref(v___x_3796_);
v___x_3798_ = lean_unsigned_to_nat(1u);
v___x_3799_ = lean_nat_add(v_currRecDepth_3786_, v___x_3798_);
lean_dec(v_currRecDepth_3786_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 1, v___x_3799_);
v___x_3801_ = v___x_3792_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_toCold_3785_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3825_, 2, v_ref_3787_);
lean_ctor_set_uint16(v_reuseFailAlloc_3825_, sizeof(void*)*3, v_optionFlags_3788_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*3 + 2, v_suppressElabErrors_3789_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*3 + 3, v_isRecordingDeps_3790_);
v___x_3801_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
uint8_t v___x_3802_; uint8_t v___x_3803_; 
v___x_3802_ = 1;
v___x_3803_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3797_, v___x_3802_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3761_, v_a_3762_, v_a_3763_, v___x_3801_, v_a_3765_);
lean_dec(v_a_3765_);
lean_dec_ref(v___x_3801_);
lean_dec(v_a_3763_);
v___y_3768_ = v___x_3804_;
goto v___jp_3767_;
}
else
{
lean_object* v_keyedConfig_3805_; uint8_t v_trackZetaDelta_3806_; lean_object* v_zetaDeltaSet_3807_; lean_object* v_lctx_3808_; lean_object* v_localInstances_3809_; lean_object* v_defEqCtx_x3f_3810_; lean_object* v_synthPendingDepth_3811_; lean_object* v_customCanUnfoldPredicate_x3f_3812_; uint8_t v_univApprox_3813_; uint8_t v_inTypeClassResolution_3814_; uint8_t v_cacheInferType_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3824_; 
v_keyedConfig_3805_ = lean_ctor_get(v_a_3762_, 0);
v_trackZetaDelta_3806_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*7);
v_zetaDeltaSet_3807_ = lean_ctor_get(v_a_3762_, 1);
v_lctx_3808_ = lean_ctor_get(v_a_3762_, 2);
v_localInstances_3809_ = lean_ctor_get(v_a_3762_, 3);
v_defEqCtx_x3f_3810_ = lean_ctor_get(v_a_3762_, 4);
v_synthPendingDepth_3811_ = lean_ctor_get(v_a_3762_, 5);
v_customCanUnfoldPredicate_x3f_3812_ = lean_ctor_get(v_a_3762_, 6);
v_univApprox_3813_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3814_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*7 + 2);
v_cacheInferType_3815_ = lean_ctor_get_uint8(v_a_3762_, sizeof(void*)*7 + 3);
v_isSharedCheck_3824_ = !lean_is_exclusive(v_a_3762_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3817_ = v_a_3762_;
v_isShared_3818_ = v_isSharedCheck_3824_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3812_);
lean_inc(v_synthPendingDepth_3811_);
lean_inc(v_defEqCtx_x3f_3810_);
lean_inc(v_localInstances_3809_);
lean_inc(v_lctx_3808_);
lean_inc(v_zetaDeltaSet_3807_);
lean_inc(v_keyedConfig_3805_);
lean_dec(v_a_3762_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3824_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3819_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3802_, v_keyedConfig_3805_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 0, v___x_3819_);
v___x_3821_ = v___x_3817_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3823_, 1, v_zetaDeltaSet_3807_);
lean_ctor_set(v_reuseFailAlloc_3823_, 2, v_lctx_3808_);
lean_ctor_set(v_reuseFailAlloc_3823_, 3, v_localInstances_3809_);
lean_ctor_set(v_reuseFailAlloc_3823_, 4, v_defEqCtx_x3f_3810_);
lean_ctor_set(v_reuseFailAlloc_3823_, 5, v_synthPendingDepth_3811_);
lean_ctor_set(v_reuseFailAlloc_3823_, 6, v_customCanUnfoldPredicate_x3f_3812_);
lean_ctor_set_uint8(v_reuseFailAlloc_3823_, sizeof(void*)*7, v_trackZetaDelta_3806_);
lean_ctor_set_uint8(v_reuseFailAlloc_3823_, sizeof(void*)*7 + 1, v_univApprox_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3823_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3814_);
lean_ctor_set_uint8(v_reuseFailAlloc_3823_, sizeof(void*)*7 + 3, v_cacheInferType_3815_);
v___x_3821_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_Meta_inferTypeImp___lam__0(v_e_3761_, v___x_3821_, v_a_3763_, v___x_3801_, v_a_3765_);
lean_dec(v_a_3765_);
lean_dec_ref(v___x_3801_);
lean_dec(v_a_3763_);
v___y_3768_ = v___x_3822_;
goto v___jp_3767_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = lean_infer_type(v_e_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3838_){
_start:
{
switch(lean_obj_tag(v_x_3838_))
{
case 0:
{
uint8_t v___x_3839_; 
v___x_3839_ = 1;
return v___x_3839_;
}
case 2:
{
lean_object* v_a_3840_; lean_object* v_a_3841_; uint8_t v___x_3842_; 
v_a_3840_ = lean_ctor_get(v_x_3838_, 0);
v_a_3841_ = lean_ctor_get(v_x_3838_, 1);
v___x_3842_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3840_);
if (v___x_3842_ == 0)
{
return v___x_3842_;
}
else
{
v_x_3838_ = v_a_3841_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3844_; 
v_a_3844_ = lean_ctor_get(v_x_3838_, 1);
v_x_3838_ = v_a_3844_;
goto _start;
}
default: 
{
uint8_t v___x_3846_; 
v___x_3846_ = 0;
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3847_){
_start:
{
uint8_t v_res_3848_; lean_object* v_r_3849_; 
v_res_3848_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3847_);
lean_dec(v_x_3847_);
v_r_3849_ = lean_box(v_res_3848_);
return v_r_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v___x_3853_; lean_object* v_mctx_3854_; lean_object* v___x_3855_; lean_object* v_fst_3856_; lean_object* v_snd_3857_; lean_object* v___x_3858_; lean_object* v_cache_3859_; lean_object* v_zetaDeltaFVarIds_3860_; lean_object* v_postponed_3861_; lean_object* v_diag_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3871_; 
v___x_3853_ = lean_st_ref_get(v___y_3851_);
v_mctx_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc_ref(v_mctx_3854_);
lean_dec(v___x_3853_);
v___x_3855_ = lean_instantiate_level_mvars(v_mctx_3854_, v_l_3850_);
v_fst_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_fst_3856_);
v_snd_3857_ = lean_ctor_get(v___x_3855_, 1);
lean_inc(v_snd_3857_);
lean_dec_ref(v___x_3855_);
v___x_3858_ = lean_st_ref_take(v___y_3851_);
v_cache_3859_ = lean_ctor_get(v___x_3858_, 1);
v_zetaDeltaFVarIds_3860_ = lean_ctor_get(v___x_3858_, 2);
v_postponed_3861_ = lean_ctor_get(v___x_3858_, 3);
v_diag_3862_ = lean_ctor_get(v___x_3858_, 4);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; 
v_unused_3872_ = lean_ctor_get(v___x_3858_, 0);
lean_dec(v_unused_3872_);
v___x_3864_ = v___x_3858_;
v_isShared_3865_ = v_isSharedCheck_3871_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_diag_3862_);
lean_inc(v_postponed_3861_);
lean_inc(v_zetaDeltaFVarIds_3860_);
lean_inc(v_cache_3859_);
lean_dec(v___x_3858_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3871_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v_fst_3856_);
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_fst_3856_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_cache_3859_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_zetaDeltaFVarIds_3860_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v_postponed_3861_);
lean_ctor_set(v_reuseFailAlloc_3870_, 4, v_diag_3862_);
v___x_3867_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_st_ref_put(v___y_3851_, v___x_3867_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v_snd_3857_);
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3873_, v___y_3874_);
lean_dec(v___y_3874_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3877_, v___y_3879_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3891_, lean_object* v_x_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
switch(lean_obj_tag(v_x_3891_))
{
case 3:
{
lean_object* v_u_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v_u_3902_ = lean_ctor_get(v_x_3891_, 0);
lean_inc(v_u_3902_);
lean_dec_ref_known(v_x_3891_, 1);
v___x_3903_ = lean_unsigned_to_nat(0u);
v___x_3904_ = lean_nat_dec_eq(v_x_3892_, v___x_3903_);
lean_dec(v_x_3892_);
if (v___x_3904_ == 0)
{
lean_dec(v_u_3902_);
goto v___jp_3898_;
}
else
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3902_, v_a_3894_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3916_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3916_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3916_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
uint8_t v___x_3910_; uint8_t v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3910_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3906_);
lean_dec(v_a_3906_);
v___x_3911_ = l_Lean_Bool_toLBool(v___x_3910_);
v___x_3912_ = lean_box(v___x_3911_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3912_);
v___x_3914_ = v___x_3908_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
v_a_3917_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3905_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3905_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3925_; lean_object* v_zero_3926_; uint8_t v_isZero_3927_; 
v_body_3925_ = lean_ctor_get(v_x_3891_, 2);
lean_inc_ref(v_body_3925_);
lean_dec_ref_known(v_x_3891_, 3);
v_zero_3926_ = lean_unsigned_to_nat(0u);
v_isZero_3927_ = lean_nat_dec_eq(v_x_3892_, v_zero_3926_);
if (v_isZero_3927_ == 1)
{
uint8_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_dec_ref(v_body_3925_);
lean_dec(v_x_3892_);
v___x_3928_ = 0;
v___x_3929_ = lean_box(v___x_3928_);
v___x_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
return v___x_3930_;
}
else
{
lean_object* v_one_3931_; lean_object* v_n_3932_; 
v_one_3931_ = lean_unsigned_to_nat(1u);
v_n_3932_ = lean_nat_sub(v_x_3892_, v_one_3931_);
lean_dec(v_x_3892_);
v_x_3891_ = v_body_3925_;
v_x_3892_ = v_n_3932_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3934_; 
v_body_3934_ = lean_ctor_get(v_x_3891_, 3);
lean_inc_ref(v_body_3934_);
lean_dec_ref_known(v_x_3891_, 4);
v_x_3891_ = v_body_3934_;
goto _start;
}
case 10:
{
lean_object* v_expr_3936_; 
v_expr_3936_ = lean_ctor_get(v_x_3891_, 1);
lean_inc_ref(v_expr_3936_);
lean_dec_ref_known(v_x_3891_, 2);
v_x_3891_ = v_expr_3936_;
goto _start;
}
default: 
{
lean_dec(v_x_3892_);
lean_dec_ref(v_x_3891_);
goto v___jp_3898_;
}
}
v___jp_3898_:
{
uint8_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3899_ = 2;
v___x_3900_ = lean_box(v___x_3899_);
v___x_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3938_, lean_object* v_x_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3938_, v_x_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3946_, lean_object* v_x_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
switch(lean_obj_tag(v_x_3946_))
{
case 4:
{
lean_object* v_declName_3953_; lean_object* v_us_3954_; lean_object* v___x_3955_; 
v_declName_3953_ = lean_ctor_get(v_x_3946_, 0);
lean_inc(v_declName_3953_);
v_us_3954_ = lean_ctor_get(v_x_3946_, 1);
lean_inc(v_us_3954_);
lean_dec_ref_known(v_x_3946_, 2);
v___x_3955_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3953_, v_us_3954_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_a_3956_);
lean_dec_ref_known(v___x_3955_, 1);
v___x_3957_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3956_, v_x_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3957_;
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec(v_x_3947_);
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
case 1:
{
lean_object* v_fvarId_3966_; lean_object* v___x_3967_; 
v_fvarId_3966_ = lean_ctor_get(v_x_3946_, 0);
lean_inc(v_fvarId_3966_);
lean_dec_ref_known(v_x_3946_, 1);
v___x_3967_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3966_, v_a_3948_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3969_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___x_3967_, 1);
v___x_3969_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3968_, v_x_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3969_;
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec(v_x_3947_);
v_a_3970_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3967_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3967_);
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
case 2:
{
lean_object* v_mvarId_3978_; lean_object* v___x_3979_; 
v_mvarId_3978_ = lean_ctor_get(v_x_3946_, 0);
lean_inc(v_mvarId_3978_);
lean_dec_ref_known(v_x_3946_, 1);
v___x_3979_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3978_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3980_, v_x_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3981_;
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v_x_3947_);
v_a_3982_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3979_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3979_);
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
case 5:
{
lean_object* v_fn_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v_fn_3990_ = lean_ctor_get(v_x_3946_, 0);
lean_inc_ref(v_fn_3990_);
lean_dec_ref_known(v_x_3946_, 2);
v___x_3991_ = lean_unsigned_to_nat(1u);
v___x_3992_ = lean_nat_add(v_x_3947_, v___x_3991_);
lean_dec(v_x_3947_);
v_x_3946_ = v_fn_3990_;
v_x_3947_ = v___x_3992_;
goto _start;
}
case 10:
{
lean_object* v_expr_3994_; 
v_expr_3994_ = lean_ctor_get(v_x_3946_, 1);
lean_inc_ref(v_expr_3994_);
lean_dec_ref_known(v_x_3946_, 2);
v_x_3946_ = v_expr_3994_;
goto _start;
}
case 8:
{
lean_object* v_body_3996_; 
v_body_3996_ = lean_ctor_get(v_x_3946_, 3);
lean_inc_ref(v_body_3996_);
lean_dec_ref_known(v_x_3946_, 4);
v_x_3946_ = v_body_3996_;
goto _start;
}
case 6:
{
lean_object* v_body_3998_; lean_object* v_zero_3999_; uint8_t v_isZero_4000_; 
v_body_3998_ = lean_ctor_get(v_x_3946_, 2);
lean_inc_ref(v_body_3998_);
lean_dec_ref_known(v_x_3946_, 3);
v_zero_3999_ = lean_unsigned_to_nat(0u);
v_isZero_4000_ = lean_nat_dec_eq(v_x_3947_, v_zero_3999_);
if (v_isZero_4000_ == 1)
{
uint8_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_dec_ref(v_body_3998_);
lean_dec(v_x_3947_);
v___x_4001_ = 0;
v___x_4002_ = lean_box(v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
return v___x_4003_;
}
else
{
lean_object* v_one_4004_; lean_object* v_n_4005_; 
v_one_4004_ = lean_unsigned_to_nat(1u);
v_n_4005_ = lean_nat_sub(v_x_3947_, v_one_4004_);
lean_dec(v_x_3947_);
v_x_3946_ = v_body_3998_;
v_x_3947_ = v_n_4005_;
goto _start;
}
}
default: 
{
uint8_t v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec(v_x_3947_);
lean_dec_ref(v_x_3946_);
v___x_4007_ = 2;
v___x_4008_ = lean_box(v___x_4007_);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_4010_, lean_object* v_x_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_4010_, v_x_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
switch(lean_obj_tag(v_x_4018_))
{
case 1:
{
lean_object* v_fvarId_4024_; lean_object* v___x_4025_; 
v_fvarId_4024_ = lean_ctor_get(v_x_4018_, 0);
lean_inc(v_fvarId_4024_);
lean_dec_ref_known(v_x_4018_, 1);
v___x_4025_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4024_, v_a_4019_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4026_, v___x_4027_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
return v___x_4028_;
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
v_a_4029_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4025_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4025_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4037_; lean_object* v___x_4038_; 
v_mvarId_4037_ = lean_ctor_get(v_x_4018_, 0);
lean_inc(v_mvarId_4037_);
lean_dec_ref_known(v_x_4018_, 1);
v___x_4038_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4037_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___x_4038_, 1);
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4039_, v___x_4040_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4038_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4038_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
case 3:
{
uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_dec_ref_known(v_x_4018_, 1);
v___x_4050_ = 0;
v___x_4051_ = lean_box(v___x_4050_);
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
case 4:
{
lean_object* v_declName_4053_; lean_object* v_us_4054_; lean_object* v___x_4055_; 
v_declName_4053_ = lean_ctor_get(v_x_4018_, 0);
lean_inc(v_declName_4053_);
v_us_4054_ = lean_ctor_get(v_x_4018_, 1);
lean_inc(v_us_4054_);
lean_dec_ref_known(v_x_4018_, 2);
v___x_4055_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4053_, v_us_4054_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4056_, v___x_4057_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
return v___x_4058_;
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
v_a_4059_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4055_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4055_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
case 5:
{
lean_object* v_fn_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_fn_4067_ = lean_ctor_get(v_x_4018_, 0);
lean_inc_ref(v_fn_4067_);
lean_dec_ref_known(v_x_4018_, 2);
v___x_4068_ = lean_unsigned_to_nat(1u);
v___x_4069_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4067_, v___x_4068_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
return v___x_4069_;
}
case 6:
{
uint8_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_dec_ref_known(v_x_4018_, 3);
v___x_4070_ = 0;
v___x_4071_ = lean_box(v___x_4070_);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
case 7:
{
lean_object* v_body_4073_; 
v_body_4073_ = lean_ctor_get(v_x_4018_, 2);
lean_inc_ref(v_body_4073_);
lean_dec_ref_known(v_x_4018_, 3);
v_x_4018_ = v_body_4073_;
goto _start;
}
case 8:
{
lean_object* v_body_4075_; 
v_body_4075_ = lean_ctor_get(v_x_4018_, 3);
lean_inc_ref(v_body_4075_);
lean_dec_ref_known(v_x_4018_, 4);
v_x_4018_ = v_body_4075_;
goto _start;
}
case 9:
{
uint8_t v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec_ref_known(v_x_4018_, 1);
v___x_4077_ = 0;
v___x_4078_ = lean_box(v___x_4077_);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
case 10:
{
lean_object* v_expr_4080_; 
v_expr_4080_ = lean_ctor_get(v_x_4018_, 1);
lean_inc_ref(v_expr_4080_);
lean_dec_ref_known(v_x_4018_, 2);
v_x_4018_ = v_expr_4080_;
goto _start;
}
default: 
{
uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec_ref(v_x_4018_);
v___x_4082_ = 2;
v___x_4083_ = lean_box(v___x_4082_);
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
return v___x_4084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_Meta_isPropQuick(v_x_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v___x_4098_; 
lean_inc_ref(v_e_4092_);
v___x_4098_ = l_Lean_Meta_isPropQuick(v_e_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4155_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4101_ = v___x_4098_;
v_isShared_4102_ = v_isSharedCheck_4155_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4155_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
uint8_t v___x_4103_; 
v___x_4103_ = lean_unbox(v_a_4099_);
lean_dec(v_a_4099_);
switch(v___x_4103_)
{
case 0:
{
uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4107_; 
lean_dec_ref(v_e_4092_);
v___x_4104_ = 0;
v___x_4105_ = lean_box(v___x_4104_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4105_);
v___x_4107_ = v___x_4101_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
case 1:
{
uint8_t v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
lean_dec_ref(v_e_4092_);
v___x_4109_ = 1;
v___x_4110_ = lean_box(v___x_4109_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4110_);
v___x_4112_ = v___x_4101_;
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
default: 
{
lean_object* v___x_4114_; 
lean_del_object(v___x_4101_);
lean_inc(v_a_4096_);
lean_inc_ref(v_a_4095_);
lean_inc(v_a_4094_);
lean_inc_ref(v_a_4093_);
v___x_4114_ = lean_infer_type(v_e_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; lean_object* v___x_4116_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref_known(v___x_4114_, 1);
v___x_4116_ = l_Lean_Meta_whnfD(v_a_4115_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4138_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4119_ = v___x_4116_;
v_isShared_4120_ = v_isSharedCheck_4138_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4116_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4138_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
if (lean_obj_tag(v_a_4117_) == 3)
{
lean_object* v_u_4121_; lean_object* v___x_4122_; lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4132_; 
lean_del_object(v___x_4119_);
v_u_4121_ = lean_ctor_get(v_a_4117_, 0);
lean_inc(v_u_4121_);
lean_dec_ref_known(v_a_4117_, 1);
v___x_4122_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4121_, v_a_4094_);
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4132_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4127_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4123_);
lean_dec(v_a_4123_);
v___x_4128_ = lean_box(v___x_4127_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v___x_4128_);
v___x_4130_ = v___x_4125_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
else
{
uint8_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
lean_dec(v_a_4117_);
v___x_4133_ = 0;
v___x_4134_ = lean_box(v___x_4133_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v___x_4134_);
v___x_4136_ = v___x_4119_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
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
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
v_a_4139_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4116_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4116_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
v_a_4147_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4114_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4114_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec_ref(v_e_4092_);
v_a_4156_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4098_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4098_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Meta_isProp(v_e_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(lean_object* v_x_4171_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_obj_tag_nat(v_x_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl___boxed(lean_object* v_x_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___impl(v_x_4173_);
lean_dec(v_x_4173_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4175_, lean_object* v_k_4176_){
_start:
{
if (lean_obj_tag(v_t_4175_) == 3)
{
lean_object* v_idx_4177_; lean_object* v_numArgs_4178_; lean_object* v___x_4179_; 
v_idx_4177_ = lean_ctor_get(v_t_4175_, 0);
lean_inc(v_idx_4177_);
v_numArgs_4178_ = lean_ctor_get(v_t_4175_, 1);
lean_inc(v_numArgs_4178_);
lean_dec_ref_known(v_t_4175_, 2);
v___x_4179_ = lean_apply_2(v_k_4176_, v_idx_4177_, v_numArgs_4178_);
return v___x_4179_;
}
else
{
lean_dec(v_t_4175_);
return v_k_4176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4180_, lean_object* v_ctorIdx_4181_, lean_object* v_t_4182_, lean_object* v_h_4183_, lean_object* v_k_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4182_, v_k_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4186_, lean_object* v_ctorIdx_4187_, lean_object* v_t_4188_, lean_object* v_h_4189_, lean_object* v_k_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4186_, v_ctorIdx_4187_, v_t_4188_, v_h_4189_, v_k_4190_);
lean_dec(v_ctorIdx_4187_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4192_, lean_object* v_false_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4192_, v_false_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4195_, lean_object* v_t_4196_, lean_object* v_h_4197_, lean_object* v_false_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4196_, v_false_4198_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4200_, lean_object* v_true_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4200_, v_true_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4203_, lean_object* v_t_4204_, lean_object* v_h_4205_, lean_object* v_true_4206_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4204_, v_true_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4208_, lean_object* v_undef_4209_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4208_, v_undef_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4211_, lean_object* v_t_4212_, lean_object* v_h_4213_, lean_object* v_undef_4214_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4212_, v_undef_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4216_, lean_object* v_bvar_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4216_, v_bvar_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4219_, lean_object* v_t_4220_, lean_object* v_h_4221_, lean_object* v_bvar_4222_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4220_, v_bvar_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4224_){
_start:
{
switch(v_x_4224_)
{
case 0:
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_box(0);
return v___x_4225_;
}
case 1:
{
lean_object* v___x_4226_; 
v___x_4226_ = lean_box(1);
return v___x_4226_;
}
default: 
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_box(2);
return v___x_4227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4228_){
_start:
{
uint8_t v_x_25__boxed_4229_; lean_object* v_res_4230_; 
v_x_25__boxed_4229_ = lean_unbox(v_x_4228_);
v_res_4230_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4229_);
return v_res_4230_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4231_){
_start:
{
switch(lean_obj_tag(v_x_4231_))
{
case 0:
{
uint8_t v___x_4232_; 
v___x_4232_ = 0;
return v___x_4232_;
}
case 1:
{
uint8_t v___x_4233_; 
v___x_4233_ = 1;
return v___x_4233_;
}
default: 
{
uint8_t v___x_4234_; 
v___x_4234_ = 2;
return v___x_4234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4235_){
_start:
{
uint8_t v_res_4236_; lean_object* v_r_4237_; 
v_res_4236_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4235_);
lean_dec(v_x_4235_);
v_r_4237_ = lean_box(v_res_4236_);
return v_r_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4239_, lean_object* v_numArgs_4240_){
_start:
{
switch(lean_obj_tag(v_e_4239_))
{
case 3:
{
lean_object* v_u_4241_; lean_object* v___x_4242_; uint8_t v___x_4243_; 
v_u_4241_ = lean_ctor_get(v_e_4239_, 0);
v___x_4242_ = lean_unsigned_to_nat(0u);
v___x_4243_ = lean_nat_dec_eq(v_numArgs_4240_, v___x_4242_);
lean_dec(v_numArgs_4240_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_box(2);
return v___x_4244_;
}
else
{
uint8_t v___x_4245_; 
v___x_4245_ = l_Lean_Level_isNeverZero(v_u_4241_);
if (v___x_4245_ == 0)
{
uint8_t v___x_4246_; 
v___x_4246_ = l_Lean_Level_isZero(v_u_4241_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; 
v___x_4247_ = lean_box(2);
return v___x_4247_;
}
else
{
lean_object* v___x_4248_; 
v___x_4248_ = lean_box(1);
return v___x_4248_;
}
}
else
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_box(0);
return v___x_4249_;
}
}
}
case 7:
{
lean_object* v_body_4250_; lean_object* v_zero_4251_; uint8_t v_isZero_4252_; 
v_body_4250_ = lean_ctor_get(v_e_4239_, 2);
v_zero_4251_ = lean_unsigned_to_nat(0u);
v_isZero_4252_ = lean_nat_dec_eq(v_numArgs_4240_, v_zero_4251_);
if (v_isZero_4252_ == 0)
{
lean_object* v_one_4253_; lean_object* v_n_4254_; 
v_one_4253_ = lean_unsigned_to_nat(1u);
v_n_4254_ = lean_nat_sub(v_numArgs_4240_, v_one_4253_);
lean_dec(v_numArgs_4240_);
v_e_4239_ = v_body_4250_;
v_numArgs_4240_ = v_n_4254_;
goto _start;
}
else
{
lean_object* v___x_4256_; 
lean_dec(v_numArgs_4240_);
v___x_4256_ = lean_box(2);
return v___x_4256_;
}
}
case 10:
{
lean_object* v_expr_4257_; 
v_expr_4257_ = lean_ctor_get(v_e_4239_, 1);
v_e_4239_ = v_expr_4257_;
goto _start;
}
case 5:
{
lean_object* v_fn_4259_; 
v_fn_4259_ = lean_ctor_get(v_e_4239_, 0);
if (lean_obj_tag(v_fn_4259_) == 4)
{
lean_object* v_declName_4260_; 
v_declName_4260_ = lean_ctor_get(v_fn_4259_, 0);
if (lean_obj_tag(v_declName_4260_) == 1)
{
lean_object* v_pre_4261_; 
v_pre_4261_ = lean_ctor_get(v_declName_4260_, 0);
if (lean_obj_tag(v_pre_4261_) == 0)
{
lean_object* v_arg_4262_; lean_object* v_str_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_arg_4262_ = lean_ctor_get(v_e_4239_, 1);
v_str_4263_ = lean_ctor_get(v_declName_4260_, 1);
v___x_4264_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4265_ = lean_string_dec_eq(v_str_4263_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; 
lean_dec(v_numArgs_4240_);
v___x_4266_ = lean_box(2);
return v___x_4266_;
}
else
{
v_e_4239_ = v_arg_4262_;
goto _start;
}
}
else
{
lean_object* v___x_4268_; 
lean_dec(v_numArgs_4240_);
v___x_4268_ = lean_box(2);
return v___x_4268_;
}
}
else
{
lean_object* v___x_4269_; 
lean_dec(v_numArgs_4240_);
v___x_4269_ = lean_box(2);
return v___x_4269_;
}
}
else
{
lean_object* v___x_4270_; 
lean_dec(v_numArgs_4240_);
v___x_4270_ = lean_box(2);
return v___x_4270_;
}
}
default: 
{
lean_object* v___x_4271_; 
lean_dec(v_numArgs_4240_);
v___x_4271_ = lean_box(2);
return v___x_4271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4272_, lean_object* v_numArgs_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4272_, v_numArgs_4273_);
lean_dec_ref(v_e_4272_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4275_, lean_object* v_binderType_4276_){
_start:
{
if (lean_obj_tag(v_r_4275_) == 3)
{
lean_object* v_idx_4277_; lean_object* v_numArgs_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4290_; 
v_idx_4277_ = lean_ctor_get(v_r_4275_, 0);
v_numArgs_4278_ = lean_ctor_get(v_r_4275_, 1);
v_isSharedCheck_4290_ = !lean_is_exclusive(v_r_4275_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4280_ = v_r_4275_;
v_isShared_4281_ = v_isSharedCheck_4290_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_numArgs_4278_);
lean_inc(v_idx_4277_);
lean_dec(v_r_4275_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4290_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v_zero_4282_; uint8_t v_isZero_4283_; 
v_zero_4282_ = lean_unsigned_to_nat(0u);
v_isZero_4283_ = lean_nat_dec_eq(v_idx_4277_, v_zero_4282_);
if (v_isZero_4283_ == 1)
{
lean_object* v___x_4284_; 
lean_del_object(v___x_4280_);
lean_dec(v_idx_4277_);
v___x_4284_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4276_, v_numArgs_4278_);
return v___x_4284_;
}
else
{
lean_object* v_one_4285_; lean_object* v_n_4286_; lean_object* v___x_4288_; 
v_one_4285_ = lean_unsigned_to_nat(1u);
v_n_4286_ = lean_nat_sub(v_idx_4277_, v_one_4285_);
lean_dec(v_idx_4277_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 0, v_n_4286_);
v___x_4288_ = v___x_4280_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_n_4286_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v_numArgs_4278_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
else
{
return v_r_4275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4291_, lean_object* v_binderType_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4291_, v_binderType_4292_);
lean_dec_ref(v_binderType_4292_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4294_, lean_object* v_x_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v_type_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; 
switch(lean_obj_tag(v_x_4294_))
{
case 7:
{
lean_object* v_binderType_4334_; lean_object* v_body_4335_; lean_object* v_zero_4336_; uint8_t v_isZero_4337_; 
v_binderType_4334_ = lean_ctor_get(v_x_4294_, 1);
v_body_4335_ = lean_ctor_get(v_x_4294_, 2);
v_zero_4336_ = lean_unsigned_to_nat(0u);
v_isZero_4337_ = lean_nat_dec_eq(v_x_4295_, v_zero_4336_);
if (v_isZero_4337_ == 1)
{
v_type_4302_ = v_x_4294_;
v___y_4303_ = v_a_4296_;
v___y_4304_ = v_a_4297_;
v___y_4305_ = v_a_4298_;
v___y_4306_ = v_a_4299_;
goto v___jp_4301_;
}
else
{
lean_object* v_one_4338_; lean_object* v_n_4339_; lean_object* v___x_4340_; 
lean_inc_ref(v_body_4335_);
lean_inc_ref(v_binderType_4334_);
lean_dec_ref_known(v_x_4294_, 3);
v_one_4338_ = lean_unsigned_to_nat(1u);
v_n_4339_ = lean_nat_sub(v_x_4295_, v_one_4338_);
v___x_4340_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4335_, v_n_4339_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
lean_dec(v_n_4339_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4349_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4343_ = v___x_4340_;
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4340_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4345_; lean_object* v___x_4347_; 
v___x_4345_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4341_, v_binderType_4334_);
lean_dec_ref(v_binderType_4334_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v___x_4345_);
v___x_4347_ = v___x_4343_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4345_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
else
{
lean_dec_ref(v_binderType_4334_);
return v___x_4340_;
}
}
}
case 8:
{
lean_object* v_type_4350_; lean_object* v_body_4351_; lean_object* v___x_4352_; 
v_type_4350_ = lean_ctor_get(v_x_4294_, 1);
lean_inc_ref(v_type_4350_);
v_body_4351_ = lean_ctor_get(v_x_4294_, 3);
lean_inc_ref(v_body_4351_);
lean_dec_ref_known(v_x_4294_, 4);
v___x_4352_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4351_, v_x_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4361_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4361_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4361_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; lean_object* v___x_4359_; 
v___x_4357_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4353_, v_type_4350_);
lean_dec_ref(v_type_4350_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4357_);
v___x_4359_ = v___x_4355_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
else
{
lean_dec_ref(v_type_4350_);
return v___x_4352_;
}
}
case 10:
{
lean_object* v_expr_4362_; 
v_expr_4362_ = lean_ctor_get(v_x_4294_, 1);
lean_inc_ref(v_expr_4362_);
lean_dec_ref_known(v_x_4294_, 2);
v_x_4294_ = v_expr_4362_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4364_; lean_object* v___x_4365_; uint8_t v___x_4366_; 
v_deBruijnIndex_4364_ = lean_ctor_get(v_x_4294_, 0);
lean_inc(v_deBruijnIndex_4364_);
lean_dec_ref_known(v_x_4294_, 1);
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = lean_nat_dec_eq(v_x_4295_, v___x_4365_);
if (v___x_4366_ == 0)
{
lean_dec(v_deBruijnIndex_4364_);
goto v___jp_4331_;
}
else
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4367_, 0, v_deBruijnIndex_4364_);
lean_ctor_set(v___x_4367_, 1, v___x_4365_);
v___x_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
return v___x_4368_;
}
}
default: 
{
lean_object* v___x_4369_; uint8_t v___x_4370_; 
v___x_4369_ = lean_unsigned_to_nat(0u);
v___x_4370_ = lean_nat_dec_eq(v_x_4295_, v___x_4369_);
if (v___x_4370_ == 0)
{
lean_dec_ref(v_x_4294_);
goto v___jp_4331_;
}
else
{
v_type_4302_ = v_x_4294_;
v___y_4303_ = v_a_4296_;
v___y_4304_ = v_a_4297_;
v___y_4305_ = v_a_4298_;
v___y_4306_ = v_a_4299_;
goto v___jp_4301_;
}
}
}
v___jp_4301_:
{
lean_object* v___x_4307_; 
v___x_4307_ = l_Lean_Expr_getAppFn(v_type_4302_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_deBruijnIndex_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_deBruijnIndex_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_deBruijnIndex_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = l_Lean_Expr_getAppNumArgs(v_type_4302_);
lean_dec_ref(v_type_4302_);
v___x_4310_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4310_, 0, v_deBruijnIndex_4308_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
return v___x_4311_;
}
else
{
lean_object* v___x_4312_; 
lean_dec_ref(v___x_4307_);
v___x_4312_ = l_Lean_Meta_isPropQuick(v_type_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4322_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4315_ = v___x_4312_;
v_isShared_4316_ = v_isSharedCheck_4322_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4312_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4322_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
uint8_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4320_; 
v___x_4317_ = lean_unbox(v_a_4313_);
lean_dec(v_a_4313_);
v___x_4318_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4317_);
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 0, v___x_4318_);
v___x_4320_ = v___x_4315_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4318_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_a_4323_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4312_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4312_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
}
v___jp_4331_:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = lean_box(2);
v___x_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
return v___x_4333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4371_, lean_object* v_x_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4371_, v_x_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_x_4372_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4379_, lean_object* v_n_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4379_, v_n_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4396_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4389_ = v___x_4386_;
v_isShared_4390_ = v_isSharedCheck_4396_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4386_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4396_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
uint8_t v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4391_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4387_);
lean_dec(v_a_4387_);
v___x_4392_ = lean_box(v___x_4391_);
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 0, v___x_4392_);
v___x_4394_ = v___x_4389_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4392_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
v_a_4397_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4386_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4386_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4405_, lean_object* v_n_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4405_, v_n_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_a_4408_);
lean_dec_ref(v_a_4407_);
lean_dec(v_n_4406_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
switch(lean_obj_tag(v_x_4413_))
{
case 1:
{
lean_object* v_fvarId_4419_; lean_object* v___x_4420_; 
v_fvarId_4419_ = lean_ctor_get(v_x_4413_, 0);
lean_inc(v_fvarId_4419_);
lean_dec_ref_known(v_x_4413_, 1);
v___x_4420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4419_, v_a_4414_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v___x_4422_ = lean_unsigned_to_nat(0u);
v___x_4423_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4421_, v___x_4422_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4423_;
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
v_a_4424_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4420_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4420_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4432_; lean_object* v___x_4433_; 
v_mvarId_4432_ = lean_ctor_get(v_x_4413_, 0);
lean_inc(v_mvarId_4432_);
lean_dec_ref_known(v_x_4413_, 1);
v___x_4433_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4432_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4434_, v___x_4435_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4436_;
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
v_a_4437_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4433_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4433_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
case 3:
{
uint8_t v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
lean_dec_ref_known(v_x_4413_, 1);
v___x_4445_ = 0;
v___x_4446_ = lean_box(v___x_4445_);
v___x_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
return v___x_4447_;
}
case 4:
{
lean_object* v_declName_4448_; lean_object* v_us_4449_; lean_object* v___x_4450_; 
v_declName_4448_ = lean_ctor_get(v_x_4413_, 0);
lean_inc(v_declName_4448_);
v_us_4449_ = lean_ctor_get(v_x_4413_, 1);
lean_inc(v_us_4449_);
lean_dec_ref_known(v_x_4413_, 2);
v___x_4450_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4448_, v_us_4449_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_a_4451_);
lean_dec_ref_known(v___x_4450_, 1);
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4451_, v___x_4452_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4453_;
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
v_a_4454_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4450_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4450_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
case 5:
{
lean_object* v_fn_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
v_fn_4462_ = lean_ctor_get(v_x_4413_, 0);
lean_inc_ref(v_fn_4462_);
lean_dec_ref_known(v_x_4413_, 2);
v___x_4463_ = lean_unsigned_to_nat(1u);
v___x_4464_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4462_, v___x_4463_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
return v___x_4464_;
}
case 6:
{
lean_object* v_body_4465_; 
v_body_4465_ = lean_ctor_get(v_x_4413_, 2);
lean_inc_ref(v_body_4465_);
lean_dec_ref_known(v_x_4413_, 3);
v_x_4413_ = v_body_4465_;
goto _start;
}
case 7:
{
uint8_t v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_dec_ref_known(v_x_4413_, 3);
v___x_4467_ = 0;
v___x_4468_ = lean_box(v___x_4467_);
v___x_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4468_);
return v___x_4469_;
}
case 8:
{
lean_object* v_body_4470_; 
v_body_4470_ = lean_ctor_get(v_x_4413_, 3);
lean_inc_ref(v_body_4470_);
lean_dec_ref_known(v_x_4413_, 4);
v_x_4413_ = v_body_4470_;
goto _start;
}
case 9:
{
uint8_t v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
lean_dec_ref_known(v_x_4413_, 1);
v___x_4472_ = 0;
v___x_4473_ = lean_box(v___x_4472_);
v___x_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
return v___x_4474_;
}
case 10:
{
lean_object* v_expr_4475_; 
v_expr_4475_ = lean_ctor_get(v_x_4413_, 1);
lean_inc_ref(v_expr_4475_);
lean_dec_ref_known(v_x_4413_, 2);
v_x_4413_ = v_expr_4475_;
goto _start;
}
default: 
{
uint8_t v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
lean_dec_ref(v_x_4413_);
v___x_4477_ = 2;
v___x_4478_ = lean_box(v___x_4477_);
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
return v___x_4479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4480_, lean_object* v_x_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
switch(lean_obj_tag(v_x_4480_))
{
case 4:
{
lean_object* v_declName_4487_; lean_object* v_us_4488_; lean_object* v___x_4489_; 
v_declName_4487_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_declName_4487_);
v_us_4488_ = lean_ctor_get(v_x_4480_, 1);
lean_inc(v_us_4488_);
lean_dec_ref_known(v_x_4480_, 2);
v___x_4489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4487_, v_us_4488_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4490_, v_x_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_x_4481_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_x_4481_);
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
case 1:
{
lean_object* v_fvarId_4500_; lean_object* v___x_4501_; 
v_fvarId_4500_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_fvarId_4500_);
lean_dec_ref_known(v_x_4480_, 1);
v___x_4501_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4500_, v_a_4482_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4503_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4502_, v_x_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_x_4481_);
return v___x_4503_;
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v_x_4481_);
v_a_4504_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4501_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4501_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4512_; lean_object* v___x_4513_; 
v_mvarId_4512_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_mvarId_4512_);
lean_dec_ref_known(v_x_4480_, 1);
v___x_4513_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4512_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4515_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
v___x_4515_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4514_, v_x_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
lean_dec(v_x_4481_);
return v___x_4515_;
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec(v_x_4481_);
v_a_4516_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4513_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4513_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
case 5:
{
lean_object* v_fn_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v_fn_4524_ = lean_ctor_get(v_x_4480_, 0);
lean_inc_ref(v_fn_4524_);
lean_dec_ref_known(v_x_4480_, 2);
v___x_4525_ = lean_unsigned_to_nat(1u);
v___x_4526_ = lean_nat_add(v_x_4481_, v___x_4525_);
lean_dec(v_x_4481_);
v_x_4480_ = v_fn_4524_;
v_x_4481_ = v___x_4526_;
goto _start;
}
case 10:
{
lean_object* v_expr_4528_; 
v_expr_4528_ = lean_ctor_get(v_x_4480_, 1);
lean_inc_ref(v_expr_4528_);
lean_dec_ref_known(v_x_4480_, 2);
v_x_4480_ = v_expr_4528_;
goto _start;
}
case 8:
{
lean_object* v_body_4530_; 
v_body_4530_ = lean_ctor_get(v_x_4480_, 3);
lean_inc_ref(v_body_4530_);
lean_dec_ref_known(v_x_4480_, 4);
v_x_4480_ = v_body_4530_;
goto _start;
}
case 6:
{
lean_object* v_body_4532_; lean_object* v_zero_4533_; uint8_t v_isZero_4534_; 
v_body_4532_ = lean_ctor_get(v_x_4480_, 2);
lean_inc_ref(v_body_4532_);
lean_dec_ref_known(v_x_4480_, 3);
v_zero_4533_ = lean_unsigned_to_nat(0u);
v_isZero_4534_ = lean_nat_dec_eq(v_x_4481_, v_zero_4533_);
if (v_isZero_4534_ == 1)
{
lean_object* v___x_4535_; 
lean_dec(v_x_4481_);
v___x_4535_ = l_Lean_Meta_isProofQuick(v_body_4532_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
return v___x_4535_;
}
else
{
lean_object* v_one_4536_; lean_object* v_n_4537_; 
v_one_4536_ = lean_unsigned_to_nat(1u);
v_n_4537_ = lean_nat_sub(v_x_4481_, v_one_4536_);
lean_dec(v_x_4481_);
v_x_4480_ = v_body_4532_;
v_x_4481_ = v_n_4537_;
goto _start;
}
}
default: 
{
uint8_t v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
lean_dec(v_x_4481_);
lean_dec_ref(v_x_4480_);
v___x_4539_ = 2;
v___x_4540_ = lean_box(v___x_4539_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
return v___x_4541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4542_, lean_object* v_x_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4542_, v_x_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l_Lean_Meta_isProofQuick(v_x_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v___x_4563_; 
lean_inc_ref(v_e_4557_);
v___x_4563_ = l_Lean_Meta_isProofQuick(v_e_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4590_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4566_ = v___x_4563_;
v_isShared_4567_ = v_isSharedCheck_4590_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4563_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4590_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
uint8_t v___x_4568_; 
v___x_4568_ = lean_unbox(v_a_4564_);
lean_dec(v_a_4564_);
switch(v___x_4568_)
{
case 0:
{
uint8_t v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
lean_dec_ref(v_e_4557_);
v___x_4569_ = 0;
v___x_4570_ = lean_box(v___x_4569_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4570_);
v___x_4572_ = v___x_4566_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
case 1:
{
uint8_t v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4577_; 
lean_dec_ref(v_e_4557_);
v___x_4574_ = 1;
v___x_4575_ = lean_box(v___x_4574_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4575_);
v___x_4577_ = v___x_4566_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4575_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
default: 
{
lean_object* v___x_4579_; 
lean_del_object(v___x_4566_);
lean_inc(v_a_4561_);
lean_inc_ref(v_a_4560_);
lean_inc(v_a_4559_);
lean_inc_ref(v_a_4558_);
v___x_4579_ = lean_infer_type(v_e_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4581_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
v___x_4581_ = l_Lean_Meta_isProp(v_a_4580_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
return v___x_4581_;
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
v_a_4582_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4579_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4579_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
lean_dec_ref(v_e_4557_);
v_a_4591_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v___x_4563_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4563_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_Meta_isProof(v_e_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4606_, lean_object* v_x_4607_){
_start:
{
switch(lean_obj_tag(v_x_4606_))
{
case 3:
{
lean_object* v___x_4613_; uint8_t v___x_4614_; 
v___x_4613_ = lean_unsigned_to_nat(0u);
v___x_4614_ = lean_nat_dec_eq(v_x_4607_, v___x_4613_);
lean_dec(v_x_4607_);
if (v___x_4614_ == 0)
{
goto v___jp_4609_;
}
else
{
uint8_t v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4615_ = 1;
v___x_4616_ = lean_box(v___x_4615_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
return v___x_4617_;
}
}
case 7:
{
lean_object* v_body_4618_; lean_object* v_zero_4619_; uint8_t v_isZero_4620_; 
v_body_4618_ = lean_ctor_get(v_x_4606_, 2);
v_zero_4619_ = lean_unsigned_to_nat(0u);
v_isZero_4620_ = lean_nat_dec_eq(v_x_4607_, v_zero_4619_);
if (v_isZero_4620_ == 1)
{
uint8_t v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
lean_dec(v_x_4607_);
v___x_4621_ = 0;
v___x_4622_ = lean_box(v___x_4621_);
v___x_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
return v___x_4623_;
}
else
{
lean_object* v_one_4624_; lean_object* v_n_4625_; 
v_one_4624_ = lean_unsigned_to_nat(1u);
v_n_4625_ = lean_nat_sub(v_x_4607_, v_one_4624_);
lean_dec(v_x_4607_);
v_x_4606_ = v_body_4618_;
v_x_4607_ = v_n_4625_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4627_; 
v_body_4627_ = lean_ctor_get(v_x_4606_, 3);
v_x_4606_ = v_body_4627_;
goto _start;
}
case 10:
{
lean_object* v_expr_4629_; 
v_expr_4629_ = lean_ctor_get(v_x_4606_, 1);
v_x_4606_ = v_expr_4629_;
goto _start;
}
default: 
{
lean_dec(v_x_4607_);
goto v___jp_4609_;
}
}
v___jp_4609_:
{
uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4610_ = 2;
v___x_4611_ = lean_box(v___x_4610_);
v___x_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
return v___x_4612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4631_, lean_object* v_x_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4631_, v_x_4632_);
lean_dec_ref(v_x_4631_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4635_, lean_object* v_x_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4635_, v_x_4636_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4643_, lean_object* v_x_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4643_, v_x_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_);
lean_dec(v_a_4648_);
lean_dec_ref(v_a_4647_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec_ref(v_x_4643_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4651_, lean_object* v_x_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_){
_start:
{
switch(lean_obj_tag(v_x_4651_))
{
case 4:
{
lean_object* v_declName_4658_; lean_object* v_us_4659_; lean_object* v___x_4660_; 
v_declName_4658_ = lean_ctor_get(v_x_4651_, 0);
lean_inc(v_declName_4658_);
v_us_4659_ = lean_ctor_get(v_x_4651_, 1);
lean_inc(v_us_4659_);
lean_dec_ref_known(v_x_4651_, 2);
v___x_4660_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4658_, v_us_4659_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4662_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
v___x_4662_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4661_, v_x_4652_);
lean_dec(v_a_4661_);
return v___x_4662_;
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec(v_x_4652_);
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
case 1:
{
lean_object* v_fvarId_4671_; lean_object* v___x_4672_; 
v_fvarId_4671_ = lean_ctor_get(v_x_4651_, 0);
lean_inc(v_fvarId_4671_);
lean_dec_ref_known(v_x_4651_, 1);
v___x_4672_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4671_, v_a_4653_, v_a_4655_, v_a_4656_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4674_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v___x_4674_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4673_, v_x_4652_);
lean_dec(v_a_4673_);
return v___x_4674_;
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
lean_dec(v_x_4652_);
v_a_4675_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4672_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4672_);
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
case 2:
{
lean_object* v_mvarId_4683_; lean_object* v___x_4684_; 
v_mvarId_4683_ = lean_ctor_get(v_x_4651_, 0);
lean_inc(v_mvarId_4683_);
lean_dec_ref_known(v_x_4651_, 1);
v___x_4684_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4683_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4686_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
v___x_4686_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4685_, v_x_4652_);
lean_dec(v_a_4685_);
return v___x_4686_;
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec(v_x_4652_);
v_a_4687_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4684_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4684_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
case 5:
{
lean_object* v_fn_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v_fn_4695_ = lean_ctor_get(v_x_4651_, 0);
lean_inc_ref(v_fn_4695_);
lean_dec_ref_known(v_x_4651_, 2);
v___x_4696_ = lean_unsigned_to_nat(1u);
v___x_4697_ = lean_nat_add(v_x_4652_, v___x_4696_);
lean_dec(v_x_4652_);
v_x_4651_ = v_fn_4695_;
v_x_4652_ = v___x_4697_;
goto _start;
}
case 10:
{
lean_object* v_expr_4699_; 
v_expr_4699_ = lean_ctor_get(v_x_4651_, 1);
lean_inc_ref(v_expr_4699_);
lean_dec_ref_known(v_x_4651_, 2);
v_x_4651_ = v_expr_4699_;
goto _start;
}
case 8:
{
lean_object* v_body_4701_; 
v_body_4701_ = lean_ctor_get(v_x_4651_, 3);
lean_inc_ref(v_body_4701_);
lean_dec_ref_known(v_x_4651_, 4);
v_x_4651_ = v_body_4701_;
goto _start;
}
case 6:
{
lean_object* v_body_4703_; lean_object* v_zero_4704_; uint8_t v_isZero_4705_; 
v_body_4703_ = lean_ctor_get(v_x_4651_, 2);
lean_inc_ref(v_body_4703_);
lean_dec_ref_known(v_x_4651_, 3);
v_zero_4704_ = lean_unsigned_to_nat(0u);
v_isZero_4705_ = lean_nat_dec_eq(v_x_4652_, v_zero_4704_);
if (v_isZero_4705_ == 1)
{
uint8_t v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
lean_dec_ref(v_body_4703_);
lean_dec(v_x_4652_);
v___x_4706_ = 0;
v___x_4707_ = lean_box(v___x_4706_);
v___x_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4707_);
return v___x_4708_;
}
else
{
lean_object* v_one_4709_; lean_object* v_n_4710_; 
v_one_4709_ = lean_unsigned_to_nat(1u);
v_n_4710_ = lean_nat_sub(v_x_4652_, v_one_4709_);
lean_dec(v_x_4652_);
v_x_4651_ = v_body_4703_;
v_x_4652_ = v_n_4710_;
goto _start;
}
}
default: 
{
uint8_t v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
lean_dec(v_x_4652_);
lean_dec_ref(v_x_4651_);
v___x_4712_ = 2;
v___x_4713_ = lean_box(v___x_4712_);
v___x_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4713_);
return v___x_4714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4715_, lean_object* v_x_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4715_, v_x_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
lean_dec(v_a_4718_);
lean_dec_ref(v_a_4717_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
switch(lean_obj_tag(v_x_4723_))
{
case 1:
{
lean_object* v_fvarId_4729_; lean_object* v___x_4730_; 
v_fvarId_4729_ = lean_ctor_get(v_x_4723_, 0);
lean_inc(v_fvarId_4729_);
lean_dec_ref_known(v_x_4723_, 1);
v___x_4730_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4729_, v_a_4724_, v_a_4726_, v_a_4727_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v___x_4732_ = lean_unsigned_to_nat(0u);
v___x_4733_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4731_, v___x_4732_);
lean_dec(v_a_4731_);
return v___x_4733_;
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
v_a_4734_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4730_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4730_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4742_; lean_object* v___x_4743_; 
v_mvarId_4742_ = lean_ctor_get(v_x_4723_, 0);
lean_inc(v_mvarId_4742_);
lean_dec_ref_known(v_x_4723_, 1);
v___x_4743_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4742_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref_known(v___x_4743_, 1);
v___x_4745_ = lean_unsigned_to_nat(0u);
v___x_4746_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4744_, v___x_4745_);
lean_dec(v_a_4744_);
return v___x_4746_;
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
v_a_4747_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4743_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4743_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
case 3:
{
uint8_t v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
lean_dec_ref_known(v_x_4723_, 1);
v___x_4755_ = 1;
v___x_4756_ = lean_box(v___x_4755_);
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
return v___x_4757_;
}
case 4:
{
lean_object* v_declName_4758_; lean_object* v_us_4759_; lean_object* v___x_4760_; 
v_declName_4758_ = lean_ctor_get(v_x_4723_, 0);
lean_inc(v_declName_4758_);
v_us_4759_ = lean_ctor_get(v_x_4723_, 1);
lean_inc(v_us_4759_);
lean_dec_ref_known(v_x_4723_, 2);
v___x_4760_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4758_, v_us_4759_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v___x_4762_ = lean_unsigned_to_nat(0u);
v___x_4763_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4761_, v___x_4762_);
lean_dec(v_a_4761_);
return v___x_4763_;
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
v_a_4764_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4760_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4760_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
case 5:
{
lean_object* v_fn_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v_fn_4772_ = lean_ctor_get(v_x_4723_, 0);
lean_inc_ref(v_fn_4772_);
lean_dec_ref_known(v_x_4723_, 2);
v___x_4773_ = lean_unsigned_to_nat(1u);
v___x_4774_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4772_, v___x_4773_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
return v___x_4774_;
}
case 6:
{
uint8_t v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
lean_dec_ref_known(v_x_4723_, 3);
v___x_4775_ = 0;
v___x_4776_ = lean_box(v___x_4775_);
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
return v___x_4777_;
}
case 7:
{
uint8_t v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
lean_dec_ref_known(v_x_4723_, 3);
v___x_4778_ = 1;
v___x_4779_ = lean_box(v___x_4778_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
case 8:
{
lean_object* v_body_4781_; 
v_body_4781_ = lean_ctor_get(v_x_4723_, 3);
lean_inc_ref(v_body_4781_);
lean_dec_ref_known(v_x_4723_, 4);
v_x_4723_ = v_body_4781_;
goto _start;
}
case 9:
{
uint8_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
lean_dec_ref_known(v_x_4723_, 1);
v___x_4783_ = 0;
v___x_4784_ = lean_box(v___x_4783_);
v___x_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
case 10:
{
lean_object* v_expr_4786_; 
v_expr_4786_ = lean_ctor_get(v_x_4723_, 1);
lean_inc_ref(v_expr_4786_);
lean_dec_ref_known(v_x_4723_, 2);
v_x_4723_ = v_expr_4786_;
goto _start;
}
default: 
{
uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
lean_dec_ref(v_x_4723_);
v___x_4788_ = 2;
v___x_4789_ = lean_box(v___x_4788_);
v___x_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4789_);
return v___x_4790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Lean_Meta_isTypeQuick(v_x_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_);
lean_dec(v_a_4795_);
lean_dec_ref(v_a_4794_);
lean_dec(v_a_4793_);
lean_dec_ref(v_a_4792_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_){
_start:
{
lean_object* v___x_4804_; 
lean_inc_ref(v_e_4798_);
v___x_4804_ = l_Lean_Meta_isTypeQuick(v_e_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4854_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4807_ = v___x_4804_;
v_isShared_4808_ = v_isSharedCheck_4854_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4804_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4854_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
uint8_t v___x_4809_; 
v___x_4809_ = lean_unbox(v_a_4805_);
lean_dec(v_a_4805_);
switch(v___x_4809_)
{
case 0:
{
uint8_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4813_; 
lean_dec_ref(v_e_4798_);
v___x_4810_ = 0;
v___x_4811_ = lean_box(v___x_4810_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 0, v___x_4811_);
v___x_4813_ = v___x_4807_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4811_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
case 1:
{
uint8_t v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4818_; 
lean_dec_ref(v_e_4798_);
v___x_4815_ = 1;
v___x_4816_ = lean_box(v___x_4815_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 0, v___x_4816_);
v___x_4818_ = v___x_4807_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4816_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
default: 
{
lean_object* v___x_4820_; 
lean_del_object(v___x_4807_);
lean_inc(v_a_4802_);
lean_inc_ref(v_a_4801_);
lean_inc(v_a_4800_);
lean_inc_ref(v_a_4799_);
v___x_4820_ = lean_infer_type(v_e_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4822_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4821_);
lean_dec_ref_known(v___x_4820_, 1);
v___x_4822_ = l_Lean_Meta_whnfD(v_a_4821_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4837_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4825_ = v___x_4822_;
v_isShared_4826_ = v_isSharedCheck_4837_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4822_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4837_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
if (lean_obj_tag(v_a_4823_) == 3)
{
uint8_t v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4830_; 
lean_dec_ref_known(v_a_4823_, 1);
v___x_4827_ = 1;
v___x_4828_ = lean_box(v___x_4827_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v___x_4828_);
v___x_4830_ = v___x_4825_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
else
{
uint8_t v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4835_; 
lean_dec(v_a_4823_);
v___x_4832_ = 0;
v___x_4833_ = lean_box(v___x_4832_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v___x_4833_);
v___x_4835_ = v___x_4825_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v___x_4833_);
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
else
{
lean_object* v_a_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4845_; 
v_a_4838_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4840_ = v___x_4822_;
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_a_4838_);
lean_dec(v___x_4822_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4845_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4843_; 
if (v_isShared_4841_ == 0)
{
v___x_4843_ = v___x_4840_;
goto v_reusejp_4842_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v_a_4838_);
v___x_4843_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4842_;
}
v_reusejp_4842_:
{
return v___x_4843_;
}
}
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
v_a_4846_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4820_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4820_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
lean_dec_ref(v_e_4798_);
v_a_4855_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4857_ = v___x_4804_;
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4804_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4858_ == 0)
{
v___x_4860_ = v___x_4857_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Lean_Meta_isType(v_e_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
lean_dec(v_a_4867_);
lean_dec_ref(v_a_4866_);
lean_dec(v_a_4865_);
lean_dec_ref(v_a_4864_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4870_){
_start:
{
switch(lean_obj_tag(v_x_4870_))
{
case 7:
{
lean_object* v_body_4871_; 
v_body_4871_ = lean_ctor_get(v_x_4870_, 2);
v_x_4870_ = v_body_4871_;
goto _start;
}
case 3:
{
lean_object* v_u_4873_; lean_object* v___x_4874_; 
v_u_4873_ = lean_ctor_get(v_x_4870_, 0);
lean_inc(v_u_4873_);
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v_u_4873_);
return v___x_4874_;
}
default: 
{
lean_object* v___x_4875_; 
v___x_4875_ = lean_box(0);
return v___x_4875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4876_);
lean_dec_ref(v_x_4876_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4878_, lean_object* v_body_4879_, lean_object* v_x_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4878_, v_body_4879_, v_x_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4889_, lean_object* v_xs_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v_l_4897_; 
switch(lean_obj_tag(v_type_4889_))
{
case 3:
{
lean_object* v_u_4900_; 
lean_dec_ref(v_xs_4890_);
v_u_4900_ = lean_ctor_get(v_type_4889_, 0);
lean_inc(v_u_4900_);
lean_dec_ref_known(v_type_4889_, 1);
v_l_4897_ = v_u_4900_;
goto v___jp_4896_;
}
case 7:
{
lean_object* v_binderName_4901_; lean_object* v_binderType_4902_; lean_object* v_body_4903_; uint8_t v_binderInfo_4904_; lean_object* v___f_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
v_binderName_4901_ = lean_ctor_get(v_type_4889_, 0);
lean_inc(v_binderName_4901_);
v_binderType_4902_ = lean_ctor_get(v_type_4889_, 1);
lean_inc_ref(v_binderType_4902_);
v_body_4903_ = lean_ctor_get(v_type_4889_, 2);
lean_inc_ref(v_body_4903_);
v_binderInfo_4904_ = lean_ctor_get_uint8(v_type_4889_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4889_, 3);
lean_inc_ref(v_xs_4890_);
v___f_4905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4905_, 0, v_xs_4890_);
lean_closure_set(v___f_4905_, 1, v_body_4903_);
v___x_4906_ = lean_expr_instantiate_rev(v_binderType_4902_, v_xs_4890_);
lean_dec_ref(v_xs_4890_);
lean_dec_ref(v_binderType_4902_);
v___x_4907_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4901_, v_binderInfo_4904_, v___x_4906_, v___f_4905_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
return v___x_4907_;
}
default: 
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = lean_expr_instantiate_rev(v_type_4889_, v_xs_4890_);
lean_dec_ref(v_xs_4890_);
lean_dec_ref(v_type_4889_);
v___x_4909_ = l_Lean_Meta_whnfD(v___x_4908_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4921_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4921_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4921_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
switch(lean_obj_tag(v_a_4910_))
{
case 3:
{
lean_object* v_u_4914_; 
lean_del_object(v___x_4912_);
v_u_4914_ = lean_ctor_get(v_a_4910_, 0);
lean_inc(v_u_4914_);
lean_dec_ref_known(v_a_4910_, 1);
v_l_4897_ = v_u_4914_;
goto v___jp_4896_;
}
case 7:
{
lean_object* v___x_4915_; 
lean_del_object(v___x_4912_);
v___x_4915_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4889_ = v_a_4910_;
v_xs_4890_ = v___x_4915_;
goto _start;
}
default: 
{
lean_object* v___x_4917_; lean_object* v___x_4919_; 
lean_dec(v_a_4910_);
v___x_4917_ = lean_box(0);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4917_);
v___x_4919_ = v___x_4912_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4917_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
v_a_4922_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4909_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4909_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
}
v___jp_4896_:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
v___x_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4898_, 0, v_l_4897_);
v___x_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4898_);
return v___x_4899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4930_, lean_object* v_body_4931_, lean_object* v_x_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4938_ = lean_array_push(v_xs_4930_, v_x_4932_);
v___x_4939_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4931_, v___x_4938_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4940_, lean_object* v_xs_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4940_, v_xs_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4948_, lean_object* v_cache_4949_, lean_object* v_a_x3f_4950_){
_start:
{
lean_object* v___x_4952_; lean_object* v_mctx_4953_; lean_object* v_zetaDeltaFVarIds_4954_; lean_object* v_postponed_4955_; lean_object* v_diag_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4966_; 
v___x_4952_ = lean_st_ref_take(v_a_4948_);
v_mctx_4953_ = lean_ctor_get(v___x_4952_, 0);
v_zetaDeltaFVarIds_4954_ = lean_ctor_get(v___x_4952_, 2);
v_postponed_4955_ = lean_ctor_get(v___x_4952_, 3);
v_diag_4956_ = lean_ctor_get(v___x_4952_, 4);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4966_ == 0)
{
lean_object* v_unused_4967_; 
v_unused_4967_ = lean_ctor_get(v___x_4952_, 1);
lean_dec(v_unused_4967_);
v___x_4958_ = v___x_4952_;
v_isShared_4959_ = v_isSharedCheck_4966_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_diag_4956_);
lean_inc(v_postponed_4955_);
lean_inc(v_zetaDeltaFVarIds_4954_);
lean_inc(v_mctx_4953_);
lean_dec(v___x_4952_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4966_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4960_; lean_object* v___x_4962_; 
v___x_4960_ = lean_box(0);
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 1, v_cache_4949_);
v___x_4962_ = v___x_4958_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_mctx_4953_);
lean_ctor_set(v_reuseFailAlloc_4965_, 1, v_cache_4949_);
lean_ctor_set(v_reuseFailAlloc_4965_, 2, v_zetaDeltaFVarIds_4954_);
lean_ctor_set(v_reuseFailAlloc_4965_, 3, v_postponed_4955_);
lean_ctor_set(v_reuseFailAlloc_4965_, 4, v_diag_4956_);
v___x_4962_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4963_ = lean_st_ref_put(v_a_4948_, v___x_4962_);
v___x_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4960_);
return v___x_4964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4968_, lean_object* v_cache_4969_, lean_object* v_a_x3f_4970_, lean_object* v___y_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4968_, v_cache_4969_, v_a_x3f_4970_);
lean_dec(v_a_x3f_4970_);
lean_dec(v_a_4968_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_){
_start:
{
lean_object* v___x_4979_; 
v___x_4979_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4973_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v_cache_4982_; lean_object* v___x_4983_; 
v___x_4980_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4981_ = lean_st_ref_get(v_a_4975_);
v_cache_4982_ = lean_ctor_get(v___x_4981_, 1);
lean_inc_ref(v_cache_4982_);
lean_dec(v___x_4981_);
v___x_4983_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4973_, v___x_4980_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_5000_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4986_ = v___x_4983_;
v_isShared_4987_ = v_isSharedCheck_5000_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4983_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_5000_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
lean_inc(v_a_4984_);
if (v_isShared_4987_ == 0)
{
lean_ctor_set_tag(v___x_4986_, 1);
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
lean_object* v___x_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
v___x_4990_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4975_, v_cache_4982_, v___x_4989_);
lean_dec_ref(v___x_4989_);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_4997_ == 0)
{
lean_object* v_unused_4998_; 
v_unused_4998_ = lean_ctor_get(v___x_4990_, 0);
lean_dec(v_unused_4998_);
v___x_4992_ = v___x_4990_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_dec(v___x_4990_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v_a_4984_);
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4984_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
v_a_5001_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_5001_);
lean_dec_ref_known(v___x_4983_, 1);
v___x_5002_ = lean_box(0);
v___x_5003_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4975_, v_cache_4982_, v___x_5002_);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5010_ == 0)
{
lean_object* v_unused_5011_; 
v_unused_5011_ = lean_ctor_get(v___x_5003_, 0);
lean_dec(v_unused_5011_);
v___x_5005_ = v___x_5003_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_dec(v___x_5003_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
lean_ctor_set_tag(v___x_5005_, 1);
lean_ctor_set(v___x_5005_, 0, v_a_5001_);
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5001_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
else
{
lean_object* v___x_5012_; 
lean_dec_ref(v_type_4973_);
v___x_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5012_, 0, v___x_4979_);
return v___x_5012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_){
_start:
{
lean_object* v___x_5026_; 
v___x_5026_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5041_; 
v_a_5027_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5029_ = v___x_5026_;
v_isShared_5030_ = v_isSharedCheck_5041_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5026_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5041_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
if (lean_obj_tag(v_a_5027_) == 0)
{
uint8_t v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5034_; 
v___x_5031_ = 0;
v___x_5032_ = lean_box(v___x_5031_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5032_);
v___x_5034_ = v___x_5029_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
else
{
uint8_t v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5039_; 
lean_dec_ref_known(v_a_5027_, 1);
v___x_5036_ = 1;
v___x_5037_ = lean_box(v___x_5036_);
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5037_);
v___x_5039_ = v___x_5029_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
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
else
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
v_a_5042_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_5026_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5026_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_Meta_isTypeFormerType(v_type_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
lean_dec(v_a_5052_);
lean_dec_ref(v_a_5051_);
return v_res_5056_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5057_, lean_object* v_x_5058_){
_start:
{
if (lean_obj_tag(v_x_5057_) == 0)
{
if (lean_obj_tag(v_x_5058_) == 0)
{
uint8_t v___x_5059_; 
v___x_5059_ = 1;
return v___x_5059_;
}
else
{
uint8_t v___x_5060_; 
v___x_5060_ = 0;
return v___x_5060_;
}
}
else
{
if (lean_obj_tag(v_x_5058_) == 0)
{
uint8_t v___x_5061_; 
v___x_5061_ = 0;
return v___x_5061_;
}
else
{
lean_object* v_val_5062_; lean_object* v_val_5063_; uint8_t v___x_5064_; 
v_val_5062_ = lean_ctor_get(v_x_5057_, 0);
v_val_5063_ = lean_ctor_get(v_x_5058_, 0);
v___x_5064_ = lean_level_eq(v_val_5062_, v_val_5063_);
return v___x_5064_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5065_, lean_object* v_x_5066_){
_start:
{
uint8_t v_res_5067_; lean_object* v_r_5068_; 
v_res_5067_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5065_, v_x_5066_);
lean_dec(v_x_5066_);
lean_dec(v_x_5065_);
v_r_5068_ = lean_box(v_res_5067_);
return v_r_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_){
_start:
{
lean_object* v___x_5077_; 
v___x_5077_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5088_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5088_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5088_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5082_; uint8_t v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5082_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5083_ = l_instBEqOption_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5078_, v___x_5082_);
lean_dec(v_a_5078_);
v___x_5084_ = lean_box(v___x_5083_);
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 0, v___x_5084_);
v___x_5086_ = v___x_5080_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
v_a_5089_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5077_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5077_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v_res_5103_; 
v_res_5103_ = l_Lean_Meta_isPropFormerType(v_type_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_){
_start:
{
lean_object* v___x_5110_; 
lean_inc(v_a_5108_);
lean_inc_ref(v_a_5107_);
lean_inc(v_a_5106_);
lean_inc_ref(v_a_5105_);
v___x_5110_ = lean_infer_type(v_e_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5112_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5110_, 1);
v___x_5112_ = l_Lean_Meta_isTypeFormerType(v_a_5111_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l_Lean_Meta_isTypeFormer(v_e_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec(v_a_5123_);
lean_dec_ref(v_a_5122_);
return v_res_5127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5128_, lean_object* v_maxFVars_x3f_5129_, lean_object* v_k_5130_, uint8_t v_cleanupAnnotations_5131_, uint8_t v_whnfType_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v___f_5138_; lean_object* v___x_5139_; 
v___f_5138_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5138_, 0, v_k_5130_);
v___x_5139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5128_, v_maxFVars_x3f_5129_, v___f_5138_, v_cleanupAnnotations_5131_, v_whnfType_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5147_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5142_ = v___x_5139_;
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5139_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
v_a_5148_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_5139_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5139_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5156_, lean_object* v_maxFVars_x3f_5157_, lean_object* v_k_5158_, lean_object* v_cleanupAnnotations_5159_, lean_object* v_whnfType_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5166_; uint8_t v_whnfType_boxed_5167_; lean_object* v_res_5168_; 
v_cleanupAnnotations_boxed_5166_ = lean_unbox(v_cleanupAnnotations_5159_);
v_whnfType_boxed_5167_ = lean_unbox(v_whnfType_5160_);
v_res_5168_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5156_, v_maxFVars_x3f_5157_, v_k_5158_, v_cleanupAnnotations_boxed_5166_, v_whnfType_boxed_5167_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5169_, lean_object* v_type_5170_, lean_object* v_maxFVars_x3f_5171_, lean_object* v_k_5172_, uint8_t v_cleanupAnnotations_5173_, uint8_t v_whnfType_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v___x_5180_; 
v___x_5180_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5170_, v_maxFVars_x3f_5171_, v_k_5172_, v_cleanupAnnotations_5173_, v_whnfType_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5181_, lean_object* v_type_5182_, lean_object* v_maxFVars_x3f_5183_, lean_object* v_k_5184_, lean_object* v_cleanupAnnotations_5185_, lean_object* v_whnfType_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5192_; uint8_t v_whnfType_boxed_5193_; lean_object* v_res_5194_; 
v_cleanupAnnotations_boxed_5192_ = lean_unbox(v_cleanupAnnotations_5185_);
v_whnfType_boxed_5193_ = lean_unbox(v_whnfType_5186_);
v_res_5194_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5181_, v_type_5182_, v_maxFVars_x3f_5183_, v_k_5184_, v_cleanupAnnotations_boxed_5192_, v_whnfType_boxed_5193_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
return v_res_5194_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5195_, lean_object* v_as_5196_, size_t v_i_5197_, size_t v_stop_5198_){
_start:
{
uint8_t v___x_5199_; 
v___x_5199_ = lean_usize_dec_eq(v_i_5197_, v_stop_5198_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; uint8_t v___x_5201_; 
v___x_5200_ = lean_array_uget_borrowed(v_as_5196_, v_i_5197_);
v___x_5201_ = lean_expr_eqv(v_a_5195_, v___x_5200_);
if (v___x_5201_ == 0)
{
size_t v___x_5202_; size_t v___x_5203_; 
v___x_5202_ = ((size_t)1ULL);
v___x_5203_ = lean_usize_add(v_i_5197_, v___x_5202_);
v_i_5197_ = v___x_5203_;
goto _start;
}
else
{
return v___x_5201_;
}
}
else
{
uint8_t v___x_5205_; 
v___x_5205_ = 0;
return v___x_5205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5206_, lean_object* v_as_5207_, lean_object* v_i_5208_, lean_object* v_stop_5209_){
_start:
{
size_t v_i_boxed_5210_; size_t v_stop_boxed_5211_; uint8_t v_res_5212_; lean_object* v_r_5213_; 
v_i_boxed_5210_ = lean_unbox_usize(v_i_5208_);
lean_dec(v_i_5208_);
v_stop_boxed_5211_ = lean_unbox_usize(v_stop_5209_);
lean_dec(v_stop_5209_);
v_res_5212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5206_, v_as_5207_, v_i_boxed_5210_, v_stop_boxed_5211_);
lean_dec_ref(v_as_5207_);
lean_dec_ref(v_a_5206_);
v_r_5213_ = lean_box(v_res_5212_);
return v_r_5213_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5214_, lean_object* v_a_5215_){
_start:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; uint8_t v___x_5218_; 
v___x_5216_ = lean_unsigned_to_nat(0u);
v___x_5217_ = lean_array_get_size(v_as_5214_);
v___x_5218_ = lean_nat_dec_lt(v___x_5216_, v___x_5217_);
if (v___x_5218_ == 0)
{
return v___x_5218_;
}
else
{
if (v___x_5218_ == 0)
{
return v___x_5218_;
}
else
{
size_t v___x_5219_; size_t v___x_5220_; uint8_t v___x_5221_; 
v___x_5219_ = ((size_t)0ULL);
v___x_5220_ = lean_usize_of_nat(v___x_5217_);
v___x_5221_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5215_, v_as_5214_, v___x_5219_, v___x_5220_);
return v___x_5221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5222_, lean_object* v_a_5223_){
_start:
{
uint8_t v_res_5224_; lean_object* v_r_5225_; 
v_res_5224_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5222_, v_a_5223_);
lean_dec_ref(v_a_5223_);
lean_dec_ref(v_as_5222_);
v_r_5225_ = lean_box(v_res_5224_);
return v_r_5225_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5226_, lean_object* v_e_5227_){
_start:
{
uint8_t v___x_5228_; lean_object* v_d_5230_; lean_object* v_b_5231_; 
v___x_5228_ = l_Lean_Expr_hasFVar(v_e_5227_);
if (v___x_5228_ == 0)
{
lean_dec_ref(v_e_5227_);
return v___x_5228_;
}
else
{
switch(lean_obj_tag(v_e_5227_))
{
case 7:
{
lean_object* v_binderType_5234_; lean_object* v_body_5235_; 
v_binderType_5234_ = lean_ctor_get(v_e_5227_, 1);
lean_inc_ref(v_binderType_5234_);
v_body_5235_ = lean_ctor_get(v_e_5227_, 2);
lean_inc_ref(v_body_5235_);
lean_dec_ref_known(v_e_5227_, 3);
v_d_5230_ = v_binderType_5234_;
v_b_5231_ = v_body_5235_;
goto v___jp_5229_;
}
case 6:
{
lean_object* v_binderType_5236_; lean_object* v_body_5237_; 
v_binderType_5236_ = lean_ctor_get(v_e_5227_, 1);
lean_inc_ref(v_binderType_5236_);
v_body_5237_ = lean_ctor_get(v_e_5227_, 2);
lean_inc_ref(v_body_5237_);
lean_dec_ref_known(v_e_5227_, 3);
v_d_5230_ = v_binderType_5236_;
v_b_5231_ = v_body_5237_;
goto v___jp_5229_;
}
case 10:
{
lean_object* v_expr_5238_; 
v_expr_5238_ = lean_ctor_get(v_e_5227_, 1);
lean_inc_ref(v_expr_5238_);
lean_dec_ref_known(v_e_5227_, 2);
v_e_5227_ = v_expr_5238_;
goto _start;
}
case 8:
{
lean_object* v_type_5240_; lean_object* v_value_5241_; lean_object* v_body_5242_; uint8_t v___x_5243_; 
v_type_5240_ = lean_ctor_get(v_e_5227_, 1);
lean_inc_ref(v_type_5240_);
v_value_5241_ = lean_ctor_get(v_e_5227_, 2);
lean_inc_ref(v_value_5241_);
v_body_5242_ = lean_ctor_get(v_e_5227_, 3);
lean_inc_ref(v_body_5242_);
lean_dec_ref_known(v_e_5227_, 4);
v___x_5243_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5226_, v_type_5240_);
if (v___x_5243_ == 0)
{
uint8_t v___x_5244_; 
v___x_5244_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5226_, v_value_5241_);
if (v___x_5244_ == 0)
{
v_e_5227_ = v_body_5242_;
goto _start;
}
else
{
lean_dec_ref(v_body_5242_);
return v___x_5228_;
}
}
else
{
lean_dec_ref(v_body_5242_);
lean_dec_ref(v_value_5241_);
return v___x_5228_;
}
}
case 5:
{
lean_object* v_fn_5246_; lean_object* v_arg_5247_; uint8_t v___x_5248_; 
v_fn_5246_ = lean_ctor_get(v_e_5227_, 0);
lean_inc_ref(v_fn_5246_);
v_arg_5247_ = lean_ctor_get(v_e_5227_, 1);
lean_inc_ref(v_arg_5247_);
lean_dec_ref_known(v_e_5227_, 2);
v___x_5248_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5226_, v_fn_5246_);
if (v___x_5248_ == 0)
{
v_e_5227_ = v_arg_5247_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5247_);
return v___x_5228_;
}
}
case 11:
{
lean_object* v_struct_5250_; 
v_struct_5250_ = lean_ctor_get(v_e_5227_, 2);
lean_inc_ref(v_struct_5250_);
lean_dec_ref_known(v_e_5227_, 3);
v_e_5227_ = v_struct_5250_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5252_; lean_object* v___x_5253_; uint8_t v___x_5254_; 
v_fvarId_5252_ = lean_ctor_get(v_e_5227_, 0);
lean_inc(v_fvarId_5252_);
lean_dec_ref_known(v_e_5227_, 1);
v___x_5253_ = l_Lean_Expr_fvar___override(v_fvarId_5252_);
v___x_5254_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5226_, v___x_5253_);
lean_dec_ref(v___x_5253_);
return v___x_5254_;
}
default: 
{
uint8_t v___x_5255_; 
lean_dec_ref(v_e_5227_);
v___x_5255_ = 0;
return v___x_5255_;
}
}
}
v___jp_5229_:
{
uint8_t v___x_5232_; 
v___x_5232_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5226_, v_d_5230_);
if (v___x_5232_ == 0)
{
v_e_5227_ = v_b_5231_;
goto _start;
}
else
{
lean_dec_ref(v_b_5231_);
return v___x_5228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5256_, lean_object* v_e_5257_){
_start:
{
uint8_t v_res_5258_; lean_object* v_r_5259_; 
v_res_5258_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5256_, v_e_5257_);
lean_dec_ref(v_xs_5256_);
v_r_5259_ = lean_box(v_res_5258_);
return v_r_5259_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5261_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5262_ = l_Lean_stringToMessageData(v___x_5261_);
return v___x_5262_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5264_; lean_object* v___x_5265_; 
v___x_5264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5265_ = l_Lean_stringToMessageData(v___x_5264_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5266_, lean_object* v_type_5267_, lean_object* v_as_5268_, size_t v_sz_5269_, size_t v_i_5270_, lean_object* v_b_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v_a_5278_; uint8_t v___x_5282_; 
v___x_5282_ = lean_usize_dec_lt(v_i_5270_, v_sz_5269_);
if (v___x_5282_ == 0)
{
lean_object* v___x_5283_; 
lean_dec_ref(v_type_5267_);
v___x_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5283_, 0, v_b_5271_);
return v___x_5283_;
}
else
{
lean_object* v___x_5284_; lean_object* v_a_5285_; uint8_t v___x_5286_; 
v___x_5284_ = lean_box(0);
v_a_5285_ = lean_array_uget_borrowed(v_as_5268_, v_i_5270_);
lean_inc(v_a_5285_);
v___x_5286_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5266_, v_a_5285_);
if (v___x_5286_ == 0)
{
v_a_5278_ = v___x_5284_;
goto v___jp_5277_;
}
else
{
lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5285_);
v___x_5288_ = l_Lean_MessageData_ofExpr(v_a_5285_);
v___x_5289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5287_);
lean_ctor_set(v___x_5289_, 1, v___x_5288_);
v___x_5290_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5289_);
lean_ctor_set(v___x_5291_, 1, v___x_5290_);
lean_inc_ref(v_type_5267_);
v___x_5292_ = l_Lean_MessageData_ofExpr(v_type_5267_);
v___x_5293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5291_);
lean_ctor_set(v___x_5293_, 1, v___x_5292_);
v___x_5294_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5293_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_dec_ref_known(v___x_5294_, 1);
v_a_5278_ = v___x_5284_;
goto v___jp_5277_;
}
else
{
lean_dec_ref(v_type_5267_);
return v___x_5294_;
}
}
}
v___jp_5277_:
{
size_t v___x_5279_; size_t v___x_5280_; 
v___x_5279_ = ((size_t)1ULL);
v___x_5280_ = lean_usize_add(v_i_5270_, v___x_5279_);
v_i_5270_ = v___x_5280_;
v_b_5271_ = v_a_5278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5295_, lean_object* v_type_5296_, lean_object* v_as_5297_, lean_object* v_sz_5298_, lean_object* v_i_5299_, lean_object* v_b_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
size_t v_sz_boxed_5306_; size_t v_i_boxed_5307_; lean_object* v_res_5308_; 
v_sz_boxed_5306_ = lean_unbox_usize(v_sz_5298_);
lean_dec(v_sz_5298_);
v_i_boxed_5307_ = lean_unbox_usize(v_i_5299_);
lean_dec(v_i_5299_);
v_res_5308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5295_, v_type_5296_, v_as_5297_, v_sz_boxed_5306_, v_i_boxed_5307_, v_b_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec_ref(v_as_5297_);
lean_dec_ref(v_xs_5295_);
return v_res_5308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5309_, size_t v_i_5310_, lean_object* v_bs_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
uint8_t v___x_5317_; 
v___x_5317_ = lean_usize_dec_lt(v_i_5310_, v_sz_5309_);
if (v___x_5317_ == 0)
{
lean_object* v___x_5318_; 
v___x_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5318_, 0, v_bs_5311_);
return v___x_5318_;
}
else
{
lean_object* v_v_5319_; lean_object* v___x_5320_; lean_object* v_bs_x27_5321_; lean_object* v___x_5322_; 
v_v_5319_ = lean_array_uget(v_bs_5311_, v_i_5310_);
v___x_5320_ = lean_unsigned_to_nat(0u);
v_bs_x27_5321_ = lean_array_uset(v_bs_5311_, v_i_5310_, v___x_5320_);
lean_inc(v___y_5315_);
lean_inc_ref(v___y_5314_);
lean_inc(v___y_5313_);
lean_inc_ref(v___y_5312_);
v___x_5322_ = lean_infer_type(v_v_5319_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; size_t v___x_5324_; size_t v___x_5325_; lean_object* v___x_5326_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref_known(v___x_5322_, 1);
v___x_5324_ = ((size_t)1ULL);
v___x_5325_ = lean_usize_add(v_i_5310_, v___x_5324_);
v___x_5326_ = lean_array_uset(v_bs_x27_5321_, v_i_5310_, v_a_5323_);
v_i_5310_ = v___x_5325_;
v_bs_5311_ = v___x_5326_;
goto _start;
}
else
{
lean_object* v_a_5328_; lean_object* v___x_5330_; uint8_t v_isShared_5331_; uint8_t v_isSharedCheck_5335_; 
lean_dec_ref(v_bs_x27_5321_);
v_a_5328_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5330_ = v___x_5322_;
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
else
{
lean_inc(v_a_5328_);
lean_dec(v___x_5322_);
v___x_5330_ = lean_box(0);
v_isShared_5331_ = v_isSharedCheck_5335_;
goto v_resetjp_5329_;
}
v_resetjp_5329_:
{
lean_object* v___x_5333_; 
if (v_isShared_5331_ == 0)
{
v___x_5333_ = v___x_5330_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5328_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5336_, lean_object* v_i_5337_, lean_object* v_bs_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
size_t v_sz_boxed_5344_; size_t v_i_boxed_5345_; lean_object* v_res_5346_; 
v_sz_boxed_5344_ = lean_unbox_usize(v_sz_5336_);
lean_dec(v_sz_5336_);
v_i_boxed_5345_ = lean_unbox_usize(v_i_5337_);
lean_dec(v_i_5337_);
v_res_5346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5344_, v_i_boxed_5345_, v_bs_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
return v_res_5346_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5348_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5349_ = l_Lean_stringToMessageData(v___x_5348_);
return v___x_5349_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5351_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5352_ = l_Lean_stringToMessageData(v___x_5351_);
return v___x_5352_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5354_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5355_ = l_Lean_stringToMessageData(v___x_5354_);
return v___x_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5356_, lean_object* v_n_5357_, lean_object* v_xs_5358_, lean_object* v_x_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_){
_start:
{
lean_object* v___x_5389_; uint8_t v___x_5390_; 
v___x_5389_ = lean_array_get_size(v_xs_5358_);
v___x_5390_ = lean_nat_dec_eq(v___x_5389_, v_n_5357_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_dec_ref(v_xs_5358_);
v___x_5391_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5392_ = l_Lean_MessageData_ofExpr(v_type_5356_);
v___x_5393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5391_);
lean_ctor_set(v___x_5393_, 1, v___x_5392_);
v___x_5394_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5395_, 0, v___x_5393_);
lean_ctor_set(v___x_5395_, 1, v___x_5394_);
v___x_5396_ = l_Nat_reprFast(v_n_5357_);
v___x_5397_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5396_);
v___x_5398_ = l_Lean_MessageData_ofFormat(v___x_5397_);
v___x_5399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5399_, 0, v___x_5395_);
lean_ctor_set(v___x_5399_, 1, v___x_5398_);
v___x_5400_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5399_);
lean_ctor_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5401_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
v_a_5403_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5402_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5402_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
else
{
lean_dec(v_n_5357_);
goto v___jp_5365_;
}
v___jp_5365_:
{
size_t v_sz_5366_; size_t v___x_5367_; lean_object* v___x_5368_; 
v_sz_5366_ = lean_array_size(v_xs_5358_);
v___x_5367_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5358_);
v___x_5368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5366_, v___x_5367_, v_xs_5358_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v_a_5369_; lean_object* v___x_5370_; size_t v_sz_5371_; lean_object* v___x_5372_; 
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
lean_inc(v_a_5369_);
lean_dec_ref_known(v___x_5368_, 1);
v___x_5370_ = lean_box(0);
v_sz_5371_ = lean_array_size(v_a_5369_);
v___x_5372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5358_, v_type_5356_, v_a_5369_, v_sz_5371_, v___x_5367_, v___x_5370_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
lean_dec_ref(v_xs_5358_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5379_; 
v_isSharedCheck_5379_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5379_ == 0)
{
lean_object* v_unused_5380_; 
v_unused_5380_ = lean_ctor_get(v___x_5372_, 0);
lean_dec(v_unused_5380_);
v___x_5374_ = v___x_5372_;
v_isShared_5375_ = v_isSharedCheck_5379_;
goto v_resetjp_5373_;
}
else
{
lean_dec(v___x_5372_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5379_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v___x_5377_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 0, v_a_5369_);
v___x_5377_ = v___x_5374_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_a_5369_);
v___x_5377_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
return v___x_5377_;
}
}
}
else
{
lean_object* v_a_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5388_; 
lean_dec(v_a_5369_);
v_a_5381_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5383_ = v___x_5372_;
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_a_5381_);
lean_dec(v___x_5372_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5388_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v___x_5386_; 
if (v_isShared_5384_ == 0)
{
v___x_5386_ = v___x_5383_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5358_);
lean_dec_ref(v_type_5356_);
return v___x_5368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5411_, lean_object* v_n_5412_, lean_object* v_xs_5413_, lean_object* v_x_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5411_, v_n_5412_, v_xs_5413_, v_x_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec_ref(v_x_5414_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5421_, lean_object* v_type_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_){
_start:
{
lean_object* v___f_5428_; lean_object* v___x_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; 
lean_inc(v_n_5421_);
lean_inc_ref(v_type_5422_);
v___f_5428_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5428_, 0, v_type_5422_);
lean_closure_set(v___f_5428_, 1, v_n_5421_);
v___x_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5429_, 0, v_n_5421_);
v___x_5430_ = 0;
v___x_5431_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5422_, v___x_5429_, v___f_5428_, v___x_5430_, v___x_5430_, v_a_5423_, v_a_5424_, v_a_5425_, v_a_5426_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5432_, lean_object* v_type_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l_Lean_Meta_arrowDomainsN(v_n_5432_, v_type_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5440_, lean_object* v_e_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v___x_5447_; 
lean_inc(v_a_5445_);
lean_inc_ref(v_a_5444_);
lean_inc(v_a_5443_);
lean_inc_ref(v_a_5442_);
v___x_5447_ = lean_infer_type(v_e_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
if (lean_obj_tag(v___x_5447_) == 0)
{
lean_object* v_a_5448_; lean_object* v___x_5449_; 
v_a_5448_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_a_5448_);
lean_dec_ref_known(v___x_5447_, 1);
v___x_5449_ = l_Lean_Meta_arrowDomainsN(v_n_5440_, v_a_5448_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_);
return v___x_5449_;
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_dec(v_n_5440_);
v_a_5450_ = lean_ctor_get(v___x_5447_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5447_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5447_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5447_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5458_, lean_object* v_e_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l_Lean_Meta_inferArgumentTypesN(v_n_5458_, v_e_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_a_5461_);
lean_dec_ref(v_a_5460_);
return v_res_5465_;
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
