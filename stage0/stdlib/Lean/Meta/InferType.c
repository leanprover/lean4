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
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
uint8_t l_Lean_Meta_instDecidableEqProjReductionKind(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
lean_object* l_instMonadEIO(lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__7(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__0_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__1;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ExprStructEq_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__6_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__7 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__7_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__8 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__8_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__9 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__9_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__10 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__10_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__0;
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__2;
static const lean_string_object l_Lean_Expr_instantiateBetaRevRange___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Expr.instantiateBetaRevRange"};
static const lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3 = (const lean_object*)&l_Lean_Expr_instantiateBetaRevRange___closed__3_value;
static const lean_string_object l_Lean_Expr_instantiateBetaRevRange___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 42, .m_data = "assertion violation: stop ≤ args.size\n    "};
static const lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__4 = (const lean_object*)&l_Lean_Expr_instantiateBetaRevRange___closed__4_value;
static lean_once_cell_t l_Lean_Expr_instantiateBetaRevRange___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__5;
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
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__7(lean_object* v_msg_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = l_Lean_instInhabitedExpr;
v___x_27_ = lean_panic_fn_borrowed(v___x_26_, v_msg_25_);
return v___x_27_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__1(void){
_start:
{
lean_object* v___x_29_; lean_object* v___f_30_; 
v___x_29_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_30_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_30_, 0, v___x_29_);
return v___f_30_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_msg_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___f_43_; lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___f_46_; lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_6666__overap_61_; lean_object* v___x_62_; 
v___x_42_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__0));
v___f_43_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__1, &l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__1_once, _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__1);
v___f_44_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_44_, 0, v___x_42_);
lean_closure_set(v___f_44_, 1, v___f_43_);
v___x_45_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__2));
v___f_46_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__3));
v___f_47_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_47_, 0, v___x_45_);
lean_closure_set(v___f_47_, 1, v___f_46_);
v___f_48_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__4));
v___f_49_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__5));
v___f_50_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__6));
v___f_51_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__7));
v___f_52_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__8));
v___f_53_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__9));
v___f_54_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___closed__10));
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___f_48_);
lean_ctor_set(v___x_55_, 1, v___f_49_);
v___x_56_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___f_50_);
lean_ctor_set(v___x_56_, 2, v___f_51_);
lean_ctor_set(v___x_56_, 3, v___f_52_);
lean_ctor_set(v___x_56_, 4, v___f_53_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___f_54_);
v___x_58_ = l_Lean_MonadStateCacheT_instMonad___redArg(v___f_44_, v___f_47_, v___x_57_);
v___x_59_ = l_Lean_instInhabitedExpr;
v___x_60_ = l_instInhabitedOfMonad___redArg(v___x_58_, v___x_59_);
v___x_6666__overap_61_ = lean_panic_fn_borrowed(v___x_60_, v_msg_40_);
lean_dec(v___x_60_);
v___x_62_ = lean_apply_1(v___x_6666__overap_61_, v___y_41_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(lean_object* v_m_63_, lean_object* v_query_64_, lean_object* v_x_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_zero_68_; uint8_t v_isZero_69_; 
v_zero_68_ = lean_unsigned_to_nat(0u);
v_isZero_69_ = lean_nat_dec_eq(v_x_66_, v_zero_68_);
if (v_isZero_69_ == 1)
{
lean_dec(v_x_67_);
lean_dec(v_x_66_);
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(2);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_val_71_ = lean_ctor_get(v_x_65_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v_x_65_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_val_71_);
lean_dec(v_x_65_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_val_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
else
{
lean_object* v_keyArray_79_; lean_object* v_valueArray_80_; lean_object* v___x_81_; uint8_t v_isSome_82_; 
v_keyArray_79_ = lean_ctor_get(v_m_63_, 1);
v_valueArray_80_ = lean_ctor_get(v_m_63_, 2);
v___x_81_ = lean_array_fget_borrowed(v_keyArray_79_, v_x_67_);
v_isSome_82_ = lean_noption_is_some(v___x_81_);
if (v_isSome_82_ == 0)
{
lean_dec(v_x_66_);
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_83_, 0, v_x_67_);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec(v_x_67_);
v_val_84_ = lean_ctor_get(v_x_65_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v_x_65_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_dec(v_x_65_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_val_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
else
{
lean_object* v_one_92_; lean_object* v_n_93_; lean_object* v___y_95_; 
v_one_92_ = lean_unsigned_to_nat(1u);
v_n_93_ = lean_nat_sub(v_x_66_, v_one_92_);
lean_dec(v_x_66_);
if (v_isSome_82_ == 0)
{
goto v___jp_101_;
}
else
{
lean_object* v___x_103_; uint8_t v_isSome_104_; 
v___x_103_ = lean_array_fget_borrowed(v_valueArray_80_, v_x_67_);
v_isSome_104_ = lean_noption_is_some(v___x_103_);
if (v_isSome_104_ == 0)
{
goto v___jp_101_;
}
else
{
lean_object* v_val_105_; lean_object* v_fst_106_; lean_object* v_snd_107_; lean_object* v_fst_108_; lean_object* v_snd_109_; lean_object* v_val_110_; uint8_t v___y_112_; uint8_t v___x_119_; 
lean_inc(v___x_81_);
v_val_105_ = lean_noption_get(v___x_81_);
v_fst_106_ = lean_ctor_get(v_val_105_, 0);
lean_inc(v_fst_106_);
v_snd_107_ = lean_ctor_get(v_val_105_, 1);
lean_inc(v_snd_107_);
v_fst_108_ = lean_ctor_get(v_query_64_, 0);
v_snd_109_ = lean_ctor_get(v_query_64_, 1);
lean_inc(v___x_103_);
v_val_110_ = lean_noption_get(v___x_103_);
v___x_119_ = l_Lean_ExprStructEq_beq(v_fst_106_, v_fst_108_);
lean_dec(v_fst_106_);
if (v___x_119_ == 0)
{
lean_dec(v_snd_107_);
v___y_112_ = v___x_119_;
goto v___jp_111_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = lean_nat_dec_eq(v_snd_107_, v_snd_109_);
lean_dec(v_snd_107_);
v___y_112_ = v___x_120_;
goto v___jp_111_;
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
lean_dec(v_val_110_);
lean_dec(v_val_105_);
v___x_113_ = lean_array_get_size(v_keyArray_79_);
v___x_114_ = lean_nat_add(v_x_67_, v_one_92_);
lean_dec(v_x_67_);
v___x_115_ = lean_nat_dec_lt(v___x_114_, v___x_113_);
if (v___x_115_ == 0)
{
lean_dec(v___x_114_);
v_x_66_ = v_n_93_;
v_x_67_ = v_zero_68_;
goto _start;
}
else
{
v_x_66_ = v_n_93_;
v_x_67_ = v___x_114_;
goto _start;
}
}
else
{
lean_object* v___x_118_; 
lean_dec(v_n_93_);
lean_dec(v_x_65_);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v_x_67_);
lean_ctor_set(v___x_118_, 1, v_val_105_);
lean_ctor_set(v___x_118_, 2, v_val_110_);
return v___x_118_;
}
}
}
}
v___jp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_96_ = lean_array_get_size(v_keyArray_79_);
v___x_97_ = lean_nat_add(v_x_67_, v_one_92_);
lean_dec(v_x_67_);
v___x_98_ = lean_nat_dec_lt(v___x_97_, v___x_96_);
if (v___x_98_ == 0)
{
lean_dec(v___x_97_);
v_x_65_ = v___y_95_;
v_x_66_ = v_n_93_;
v_x_67_ = v_zero_68_;
goto _start;
}
else
{
v_x_65_ = v___y_95_;
v_x_66_ = v_n_93_;
v_x_67_ = v___x_97_;
goto _start;
}
}
v___jp_101_:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v___x_102_; 
lean_inc(v_x_67_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_x_67_);
v___y_95_ = v___x_102_;
goto v___jp_94_;
}
else
{
v___y_95_ = v_x_65_;
goto v___jp_94_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg___boxed(lean_object* v_m_121_, lean_object* v_query_122_, lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_m_121_, v_query_122_, v_x_123_, v_x_124_, v_x_125_);
lean_dec_ref(v_query_122_);
lean_dec_ref(v_m_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(lean_object* v_m_127_, lean_object* v_query_128_){
_start:
{
lean_object* v_keyArray_129_; lean_object* v_fst_130_; lean_object* v_snd_131_; lean_object* v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v_fold_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_keyArray_129_ = lean_ctor_get(v_m_127_, 1);
v_fst_130_ = lean_ctor_get(v_query_128_, 0);
v_snd_131_ = lean_ctor_get(v_query_128_, 1);
v___x_132_ = lean_array_get_size(v_keyArray_129_);
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
v___x_147_ = lean_usize_to_nat(v___x_146_);
v___x_148_ = lean_box(0);
v___x_149_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_m_127_, v_query_128_, v___x_148_, v___x_132_, v___x_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg___boxed(lean_object* v_m_150_, lean_object* v_query_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_150_, v_query_151_);
lean_dec_ref(v_query_151_);
lean_dec_ref(v_m_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(lean_object* v_m_153_, lean_object* v_query_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_153_, v_query_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_index_156_; lean_object* v_key_157_; lean_object* v_value_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_index_156_ = lean_ctor_get(v___x_155_, 0);
v_key_157_ = lean_ctor_get(v___x_155_, 1);
v_value_158_ = lean_ctor_get(v___x_155_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_155_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_value_158_);
lean_inc(v_key_157_);
lean_inc(v_index_156_);
lean_dec(v___x_155_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_index_156_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_key_157_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_value_158_);
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
lean_object* v___x_166_; 
lean_dec(v___x_155_);
v___x_166_ = lean_box(1);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg___boxed(lean_object* v_m_167_, lean_object* v_query_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_m_167_, v_query_168_);
lean_dec_ref(v_query_168_);
lean_dec_ref(v_m_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_m_170_, v_a_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_value_173_; lean_object* v___x_174_; 
v_value_173_ = lean_ctor_get(v___x_172_, 2);
lean_inc(v_value_173_);
lean_dec_ref_known(v___x_172_, 3);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_value_173_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg___boxed(lean_object* v_m_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_176_, v_a_177_);
lean_dec_ref(v_a_177_);
lean_dec_ref(v_m_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___redArg(lean_object* v_b_179_, lean_object* v_acc_180_, lean_object* v_i_181_){
_start:
{
lean_object* v___y_183_; lean_object* v_keyArray_191_; lean_object* v_valueArray_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_keyArray_191_ = lean_ctor_get(v_b_179_, 1);
v_valueArray_192_ = lean_ctor_get(v_b_179_, 2);
v___x_193_ = lean_array_get_size(v_keyArray_191_);
v___x_194_ = lean_nat_dec_lt(v_i_181_, v___x_193_);
if (v___x_194_ == 0)
{
lean_dec(v_i_181_);
return v_acc_180_;
}
else
{
lean_object* v___x_195_; uint8_t v_isSome_196_; 
v___x_195_ = lean_array_fget_borrowed(v_keyArray_191_, v_i_181_);
v_isSome_196_ = lean_noption_is_some(v___x_195_);
if (v_isSome_196_ == 0)
{
goto v___jp_187_;
}
else
{
lean_object* v___x_197_; uint8_t v_isSome_198_; 
v___x_197_ = lean_array_fget_borrowed(v_valueArray_192_, v_i_181_);
v_isSome_198_ = lean_noption_is_some(v___x_197_);
if (v_isSome_198_ == 0)
{
goto v___jp_187_;
}
else
{
lean_object* v_val_199_; lean_object* v_val_200_; lean_object* v_i_202_; lean_object* v___x_207_; 
lean_inc(v___x_195_);
v_val_199_ = lean_noption_get(v___x_195_);
lean_inc(v___x_197_);
v_val_200_ = lean_noption_get(v___x_197_);
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_acc_180_, v_val_199_);
switch(lean_obj_tag(v___x_207_))
{
case 0:
{
lean_object* v_index_208_; lean_object* v_size_209_; lean_object* v___x_210_; 
v_index_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_index_208_);
lean_dec_ref_known(v___x_207_, 3);
v_size_209_ = lean_ctor_get(v_acc_180_, 0);
lean_inc(v_size_209_);
v___x_210_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_180_, v_size_209_, v_index_208_, v_val_199_, v_val_200_);
lean_dec(v_index_208_);
v___y_183_ = v___x_210_;
goto v___jp_182_;
}
case 1:
{
lean_object* v_index_211_; 
v_index_211_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_207_, 1);
v_i_202_ = v_index_211_;
goto v___jp_201_;
}
default: 
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_180_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_index_214_; 
v_index_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_index_214_);
lean_dec_ref_known(v___x_213_, 1);
v_i_202_ = v_index_214_;
goto v___jp_201_;
}
else
{
lean_dec(v_val_200_);
lean_dec(v_val_199_);
v___y_183_ = v_acc_180_;
goto v___jp_182_;
}
}
}
v___jp_201_:
{
lean_object* v_size_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_size_203_ = lean_ctor_get(v_acc_180_, 0);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_add(v_size_203_, v___x_204_);
v___x_206_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_180_, v___x_205_, v_i_202_, v_val_199_, v_val_200_);
lean_dec(v_i_202_);
v___y_183_ = v___x_206_;
goto v___jp_182_;
}
}
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = lean_nat_add(v_i_181_, v___x_184_);
lean_dec(v_i_181_);
v_acc_180_ = v___y_183_;
v_i_181_ = v___x_185_;
goto _start;
}
v___jp_187_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_nat_add(v_i_181_, v___x_188_);
lean_dec(v_i_181_);
v_i_181_ = v___x_189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_b_215_, lean_object* v_acc_216_, lean_object* v_i_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___redArg(v_b_215_, v_acc_216_, v_i_217_);
lean_dec_ref(v_b_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___redArg(lean_object* v_init_219_, lean_object* v_b_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___redArg(v_b_220_, v_init_219_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___redArg___boxed(lean_object* v_init_223_, lean_object* v_b_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___redArg(v_init_223_, v_b_224_);
lean_dec_ref(v_b_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(lean_object* v_m_226_){
_start:
{
lean_object* v_keyArray_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_cellCount_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_target_234_; lean_object* v___x_235_; 
v_keyArray_227_ = lean_ctor_get(v_m_226_, 1);
v___x_228_ = lean_array_get_size(v_keyArray_227_);
v___x_229_ = lean_unsigned_to_nat(2u);
v_cellCount_230_ = lean_nat_mul(v___x_228_, v___x_229_);
v___x_231_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_230_);
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_230_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_230_);
v_target_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_234_, 0, v___x_231_);
lean_ctor_set(v_target_234_, 1, v___x_232_);
lean_ctor_set(v_target_234_, 2, v___x_233_);
v___x_235_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___redArg(v_target_234_, v_m_226_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg___boxed(lean_object* v_m_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v_m_236_);
lean_dec_ref(v_m_236_);
return v_res_237_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_242_ = lean_unsigned_to_nat(21u);
v___x_243_ = lean_unsigned_to_nat(96u);
v___x_244_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_246_ = l_mkPanicMessageWithDecl(v___x_245_, v___x_244_, v___x_243_, v___x_242_, v___x_241_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_248_ = lean_unsigned_to_nat(21u);
v___x_249_ = lean_unsigned_to_nat(97u);
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_252_ = l_mkPanicMessageWithDecl(v___x_251_, v___x_250_, v___x_249_, v___x_248_, v___x_247_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_254_ = lean_unsigned_to_nat(21u);
v___x_255_ = lean_unsigned_to_nat(98u);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_258_ = l_mkPanicMessageWithDecl(v___x_257_, v___x_256_, v___x_255_, v___x_254_, v___x_253_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_260_ = lean_unsigned_to_nat(21u);
v___x_261_ = lean_unsigned_to_nat(95u);
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_264_ = l_mkPanicMessageWithDecl(v___x_263_, v___x_262_, v___x_261_, v___x_260_, v___x_259_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(lean_object* v_start_265_, lean_object* v_stop_266_, lean_object* v_args_267_, lean_object* v_e_268_, lean_object* v_offset_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = l_Lean_Expr_looseBVarRange(v_e_268_);
v___x_272_ = lean_nat_dec_le(v___x_271_, v_offset_269_);
lean_dec(v___x_271_);
if (v___x_272_ == 0)
{
if (lean_obj_tag(v_e_268_) == 5)
{
lean_object* v_fn_273_; lean_object* v_arg_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_fn_273_ = lean_ctor_get(v_e_268_, 0);
lean_inc_ref(v_fn_273_);
v_arg_274_ = lean_ctor_get(v_e_268_, 1);
lean_inc_ref(v_arg_274_);
lean_inc(v_offset_269_);
lean_inc_ref(v_e_268_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v_e_268_);
lean_ctor_set(v___x_275_, 1, v_offset_269_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_270_, v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_357_; 
v___x_277_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_265_, v_stop_266_, v_args_267_, v_e_268_, v_fn_273_, v_arg_274_, v_offset_269_, v_a_270_);
v_fst_278_ = lean_ctor_get(v___x_277_, 0);
v_snd_279_ = lean_ctor_get(v___x_277_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_357_ == 0)
{
v___x_281_ = v___x_277_;
v_isShared_282_ = v_isSharedCheck_357_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snd_279_);
lean_inc(v_fst_278_);
lean_dec(v___x_277_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_357_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___y_284_; lean_object* v_i_285_; lean_object* v___y_294_; lean_object* v___y_306_; lean_object* v_i_307_; lean_object* v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_279_, v___x_275_);
switch(lean_obj_tag(v___x_325_))
{
case 0:
{
lean_object* v_index_326_; lean_object* v_size_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_del_object(v___x_281_);
v_index_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_index_326_);
lean_dec_ref_known(v___x_325_, 3);
v_size_327_ = lean_ctor_get(v_snd_279_, 0);
lean_inc(v_size_327_);
lean_inc(v_fst_278_);
v___x_328_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_279_, v_size_327_, v_index_326_, v___x_275_, v_fst_278_);
lean_dec(v_index_326_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_fst_278_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
case 1:
{
lean_object* v_index_330_; lean_object* v_size_331_; lean_object* v_keyArray_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
lean_del_object(v___x_281_);
v_index_330_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_index_330_);
lean_dec_ref_known(v___x_325_, 1);
v_size_331_ = lean_ctor_get(v_snd_279_, 0);
v_keyArray_332_ = lean_ctor_get(v_snd_279_, 1);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_size_331_, v___x_333_);
v___x_335_ = lean_array_get_size(v_keyArray_332_);
v___x_336_ = lean_nat_dec_lt(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_dec(v___x_334_);
lean_dec(v_index_330_);
goto v___jp_313_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_337_ = lean_unsigned_to_nat(4u);
v___x_338_ = lean_nat_mul(v___x_334_, v___x_337_);
v___x_339_ = lean_unsigned_to_nat(3u);
v___x_340_ = lean_nat_mul(v___x_335_, v___x_339_);
v___x_341_ = lean_nat_dec_le(v___x_338_, v___x_340_);
lean_dec(v___x_340_);
lean_dec(v___x_338_);
if (v___x_341_ == 0)
{
lean_dec(v___x_334_);
lean_dec(v_index_330_);
goto v___jp_313_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_inc(v_fst_278_);
v___x_342_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_279_, v___x_334_, v_index_330_, v___x_275_, v_fst_278_);
lean_dec(v_index_330_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_fst_278_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
return v___x_343_;
}
}
}
default: 
{
lean_object* v_size_344_; lean_object* v_keyArray_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_size_344_ = lean_ctor_get(v_snd_279_, 0);
v_keyArray_345_ = lean_ctor_get(v_snd_279_, 1);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_size_344_, v___x_346_);
v___x_348_ = lean_array_get_size(v_keyArray_345_);
v___x_349_ = lean_nat_dec_lt(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec(v___x_347_);
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v_snd_279_);
lean_dec(v_snd_279_);
v___y_294_ = v___x_350_;
goto v___jp_293_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_351_ = lean_unsigned_to_nat(4u);
v___x_352_ = lean_nat_mul(v___x_347_, v___x_351_);
lean_dec(v___x_347_);
v___x_353_ = lean_unsigned_to_nat(3u);
v___x_354_ = lean_nat_mul(v___x_348_, v___x_353_);
v___x_355_ = lean_nat_dec_le(v___x_352_, v___x_354_);
lean_dec(v___x_354_);
lean_dec(v___x_352_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v_snd_279_);
lean_dec(v_snd_279_);
v___y_294_ = v___x_356_;
goto v___jp_293_;
}
else
{
v___y_294_ = v_snd_279_;
goto v___jp_293_;
}
}
}
}
v___jp_283_:
{
lean_object* v_size_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v_size_286_ = lean_ctor_get(v___y_284_, 0);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_size_286_, v___x_287_);
lean_inc(v_fst_278_);
v___x_289_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_284_, v___x_288_, v_i_285_, v___x_275_, v_fst_278_);
lean_dec(v_i_285_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_289_);
v___x_291_ = v___x_281_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fst_278_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
v___jp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v___y_294_, v___x_275_);
switch(lean_obj_tag(v___x_295_))
{
case 0:
{
lean_object* v_index_296_; lean_object* v_size_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_del_object(v___x_281_);
v_index_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_index_296_);
lean_dec_ref_known(v___x_295_, 3);
v_size_297_ = lean_ctor_get(v___y_294_, 0);
lean_inc(v_size_297_);
lean_inc(v_fst_278_);
v___x_298_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_294_, v_size_297_, v_index_296_, v___x_275_, v_fst_278_);
lean_dec(v_index_296_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_fst_278_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
case 1:
{
lean_object* v_index_300_; 
v_index_300_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_295_, 1);
v___y_284_ = v___y_294_;
v_i_285_ = v_index_300_;
goto v___jp_283_;
}
default: 
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_294_, v___x_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_index_303_; 
v_index_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_index_303_);
lean_dec_ref_known(v___x_302_, 1);
v___y_284_ = v___y_294_;
v_i_285_ = v_index_303_;
goto v___jp_283_;
}
else
{
lean_object* v___x_304_; 
lean_del_object(v___x_281_);
lean_dec_ref_known(v___x_275_, 2);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_fst_278_);
lean_ctor_set(v___x_304_, 1, v___y_294_);
return v___x_304_;
}
}
}
}
v___jp_305_:
{
lean_object* v_size_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_size_308_ = lean_ctor_get(v___y_306_, 0);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_size_308_, v___x_309_);
lean_inc(v_fst_278_);
v___x_311_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_306_, v___x_310_, v_i_307_, v___x_275_, v_fst_278_);
lean_dec(v_i_307_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_fst_278_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
return v___x_312_;
}
v___jp_313_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v_snd_279_);
lean_dec(v_snd_279_);
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v___x_314_, v___x_275_);
switch(lean_obj_tag(v___x_315_))
{
case 0:
{
lean_object* v_index_316_; lean_object* v_size_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_index_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_index_316_);
lean_dec_ref_known(v___x_315_, 3);
v_size_317_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_size_317_);
lean_inc(v_fst_278_);
v___x_318_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_314_, v_size_317_, v_index_316_, v___x_275_, v_fst_278_);
lean_dec(v_index_316_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_fst_278_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
case 1:
{
lean_object* v_index_320_; 
v_index_320_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_index_320_);
lean_dec_ref_known(v___x_315_, 1);
v___y_306_ = v___x_314_;
v_i_307_ = v_index_320_;
goto v___jp_305_;
}
default: 
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_314_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_index_323_; 
v_index_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_index_323_);
lean_dec_ref_known(v___x_322_, 1);
v___y_306_ = v___x_314_;
v_i_307_ = v_index_323_;
goto v___jp_305_;
}
else
{
lean_object* v___x_324_; 
lean_dec_ref_known(v___x_275_, 2);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_fst_278_);
lean_ctor_set(v___x_324_, 1, v___x_314_);
return v___x_324_;
}
}
}
}
}
}
else
{
lean_object* v_val_358_; lean_object* v___x_359_; 
lean_dec_ref_known(v___x_275_, 2);
lean_dec_ref(v_arg_274_);
lean_dec_ref_known(v_e_268_, 2);
lean_dec_ref(v_fn_273_);
lean_dec(v_offset_269_);
v_val_358_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_val_358_);
lean_dec_ref_known(v___x_276_, 1);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_val_358_);
lean_ctor_set(v___x_359_, 1, v_a_270_);
return v___x_359_;
}
}
else
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_265_, v_stop_266_, v_args_267_, v_e_268_, v_offset_269_, v_a_270_);
return v___x_360_;
}
}
else
{
lean_object* v___x_361_; 
lean_dec(v_offset_269_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_e_268_);
lean_ctor_set(v___x_361_, 1, v_a_270_);
return v___x_361_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__2));
v___x_366_ = lean_unsigned_to_nat(18u);
v___x_367_ = lean_unsigned_to_nat(1847u);
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__1));
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__0));
v___x_370_ = l_mkPanicMessageWithDecl(v___x_369_, v___x_368_, v___x_367_, v___x_366_, v___x_365_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(lean_object* v_start_371_, lean_object* v_stop_372_, lean_object* v_args_373_, lean_object* v_e_374_, lean_object* v_f_375_, lean_object* v_a_376_, lean_object* v_offset_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_414_; 
lean_inc(v_offset_377_);
v___x_379_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_371_, v_stop_372_, v_args_373_, v_f_375_, v_offset_377_, v_a_378_);
v_fst_380_ = lean_ctor_get(v___x_379_, 0);
v_snd_381_ = lean_ctor_get(v___x_379_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_414_ == 0)
{
v___x_383_ = v___x_379_;
v_isShared_384_ = v_isSharedCheck_414_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_inc(v_fst_380_);
lean_dec(v___x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_414_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v_fst_386_; lean_object* v_snd_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_413_; 
v___x_385_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_371_, v_stop_372_, v_args_373_, v_a_376_, v_offset_377_, v_snd_381_);
v_fst_386_ = lean_ctor_get(v___x_385_, 0);
v_snd_387_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_413_ == 0)
{
v___x_389_ = v___x_385_;
v_isShared_390_ = v_isSharedCheck_413_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snd_387_);
lean_inc(v_fst_386_);
lean_dec(v___x_385_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_413_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___y_392_; 
if (lean_obj_tag(v_e_374_) == 5)
{
lean_object* v_fn_400_; lean_object* v_arg_401_; size_t v___x_402_; size_t v___x_403_; uint8_t v___x_404_; 
lean_del_object(v___x_383_);
v_fn_400_ = lean_ctor_get(v_e_374_, 0);
v_arg_401_ = lean_ctor_get(v_e_374_, 1);
v___x_402_ = lean_ptr_addr(v_fn_400_);
v___x_403_ = lean_ptr_addr(v_fst_380_);
v___x_404_ = lean_usize_dec_eq(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
v___y_392_ = v___x_404_;
goto v___jp_391_;
}
else
{
size_t v___x_405_; size_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = lean_ptr_addr(v_arg_401_);
v___x_406_ = lean_ptr_addr(v_fst_386_);
v___x_407_ = lean_usize_dec_eq(v___x_405_, v___x_406_);
v___y_392_ = v___x_407_;
goto v___jp_391_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
lean_del_object(v___x_389_);
lean_dec(v_fst_386_);
lean_dec(v_fst_380_);
lean_dec_ref(v_e_374_);
v___x_408_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___closed__3);
v___x_409_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__7(v___x_408_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_snd_387_);
lean_ctor_set(v___x_383_, 0, v___x_409_);
v___x_411_ = v___x_383_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_snd_387_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
v___jp_391_:
{
if (v___y_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_395_; 
lean_dec_ref(v_e_374_);
v___x_393_ = l_Lean_Expr_app___override(v_fst_380_, v_fst_386_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_393_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_snd_387_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
else
{
lean_object* v___x_398_; 
lean_dec(v_fst_386_);
lean_dec(v_fst_380_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_e_374_);
v___x_398_ = v___x_389_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_e_374_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_snd_387_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_415_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_416_ = lean_unsigned_to_nat(21u);
v___x_417_ = lean_unsigned_to_nat(99u);
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_419_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_420_ = l_mkPanicMessageWithDecl(v___x_419_, v___x_418_, v___x_417_, v___x_416_, v___x_415_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object* v_start_421_, lean_object* v_stop_422_, lean_object* v_args_423_, lean_object* v_e_424_, lean_object* v_offset_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = l_Lean_Expr_looseBVarRange(v_e_424_);
v___x_428_ = lean_nat_dec_le(v___x_427_, v_offset_425_);
lean_dec(v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v_i_433_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v_i_455_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v___y_511_; lean_object* v___x_514_; 
lean_inc(v_offset_425_);
lean_inc_ref(v_e_424_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_e_424_);
lean_ctor_set(v___x_429_, 1, v_offset_425_);
v___x_514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_a_426_, v___x_429_);
if (lean_obj_tag(v___x_514_) == 0)
{
switch(lean_obj_tag(v_e_424_))
{
case 0:
{
lean_object* v_deBruijnIndex_515_; lean_object* v___x_516_; 
v_deBruijnIndex_515_ = lean_ctor_get(v_e_424_, 0);
lean_inc(v_deBruijnIndex_515_);
lean_dec_ref_known(v_e_424_, 1);
v___x_516_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitBVar(v_start_421_, v_stop_422_, v_args_423_, v_deBruijnIndex_515_, v_offset_425_);
lean_dec(v_offset_425_);
lean_dec(v_deBruijnIndex_515_);
v_fst_476_ = v___x_516_;
v_snd_477_ = v_a_426_;
goto v___jp_475_;
}
case 1:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec_ref_known(v_e_424_, 1);
lean_dec(v_offset_425_);
v___x_517_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3);
v___x_518_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v___x_517_, v_a_426_);
v___y_511_ = v___x_518_;
goto v___jp_510_;
}
case 2:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref_known(v_e_424_, 1);
lean_dec(v_offset_425_);
v___x_519_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4);
v___x_520_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v___x_519_, v_a_426_);
v___y_511_ = v___x_520_;
goto v___jp_510_;
}
case 3:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec_ref_known(v_e_424_, 1);
lean_dec(v_offset_425_);
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5);
v___x_522_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v___x_521_, v_a_426_);
v___y_511_ = v___x_522_;
goto v___jp_510_;
}
case 4:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref_known(v_e_424_, 2);
lean_dec(v_offset_425_);
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6);
v___x_524_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v___x_523_, v_a_426_);
v___y_511_ = v___x_524_;
goto v___jp_510_;
}
case 5:
{
lean_object* v_fn_525_; lean_object* v_arg_526_; lean_object* v_head_527_; uint8_t v___x_528_; 
v_fn_525_ = lean_ctor_get(v_e_424_, 0);
v_arg_526_ = lean_ctor_get(v_e_424_, 1);
v_head_527_ = l_Lean_Expr_getAppFn(v_e_424_);
v___x_528_ = l_Lean_Expr_isBVar(v_head_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_inc_ref(v_arg_526_);
lean_inc_ref(v_fn_525_);
lean_dec_ref(v_head_527_);
v___x_529_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_421_, v_stop_422_, v_args_423_, v_e_424_, v_fn_525_, v_arg_526_, v_offset_425_, v_a_426_);
v___y_511_ = v___x_529_;
goto v___jp_510_;
}
else
{
lean_object* v___x_530_; lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; size_t v_sz_536_; size_t v___x_537_; lean_object* v___x_538_; lean_object* v_fst_539_; lean_object* v_snd_540_; lean_object* v___x_541_; 
lean_inc(v_offset_425_);
v___x_530_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_head_527_, v_offset_425_, v_a_426_);
v_fst_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_fst_531_);
v_snd_532_ = lean_ctor_get(v___x_530_, 1);
lean_inc(v_snd_532_);
lean_dec_ref(v___x_530_);
v___x_533_ = l_Lean_Expr_getAppNumArgs(v_e_424_);
v___x_534_ = lean_mk_empty_array_with_capacity(v___x_533_);
lean_dec(v___x_533_);
v___x_535_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_424_, v___x_534_);
v_sz_536_ = lean_array_size(v___x_535_);
v___x_537_ = ((size_t)0ULL);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__5(v_start_421_, v_stop_422_, v_args_423_, v_offset_425_, v_sz_536_, v___x_537_, v___x_535_, v_snd_532_);
v_fst_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_fst_539_);
v_snd_540_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_540_);
lean_dec_ref(v___x_538_);
v___x_541_ = l_Lean_Expr_betaRev(v_fst_531_, v_fst_539_, v___x_428_, v___x_428_);
lean_dec(v_fst_539_);
v_fst_476_ = v___x_541_;
v_snd_477_ = v_snd_540_;
goto v___jp_475_;
}
}
case 6:
{
lean_object* v_binderName_542_; lean_object* v_binderType_543_; lean_object* v_body_544_; uint8_t v_binderInfo_545_; lean_object* v___x_546_; lean_object* v_fst_547_; lean_object* v_snd_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_fst_552_; lean_object* v_snd_553_; uint8_t v___y_555_; size_t v___x_559_; size_t v___x_560_; uint8_t v___x_561_; 
v_binderName_542_ = lean_ctor_get(v_e_424_, 0);
v_binderType_543_ = lean_ctor_get(v_e_424_, 1);
v_body_544_ = lean_ctor_get(v_e_424_, 2);
v_binderInfo_545_ = lean_ctor_get_uint8(v_e_424_, sizeof(void*)*3 + 8);
lean_inc(v_offset_425_);
lean_inc_ref(v_binderType_543_);
v___x_546_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_binderType_543_, v_offset_425_, v_a_426_);
v_fst_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_fst_547_);
v_snd_548_ = lean_ctor_get(v___x_546_, 1);
lean_inc(v_snd_548_);
lean_dec_ref(v___x_546_);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_offset_425_, v___x_549_);
lean_dec(v_offset_425_);
lean_inc_ref(v_body_544_);
v___x_551_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_body_544_, v___x_550_, v_snd_548_);
v_fst_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_fst_552_);
v_snd_553_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_snd_553_);
lean_dec_ref(v___x_551_);
v___x_559_ = lean_ptr_addr(v_binderType_543_);
v___x_560_ = lean_ptr_addr(v_fst_547_);
v___x_561_ = lean_usize_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
v___y_555_ = v___x_561_;
goto v___jp_554_;
}
else
{
size_t v___x_562_; size_t v___x_563_; uint8_t v___x_564_; 
v___x_562_ = lean_ptr_addr(v_body_544_);
v___x_563_ = lean_ptr_addr(v_fst_552_);
v___x_564_ = lean_usize_dec_eq(v___x_562_, v___x_563_);
v___y_555_ = v___x_564_;
goto v___jp_554_;
}
v___jp_554_:
{
if (v___y_555_ == 0)
{
lean_object* v___x_556_; 
lean_inc(v_binderName_542_);
lean_dec_ref_known(v_e_424_, 3);
v___x_556_ = l_Lean_Expr_lam___override(v_binderName_542_, v_fst_547_, v_fst_552_, v_binderInfo_545_);
v_fst_476_ = v___x_556_;
v_snd_477_ = v_snd_553_;
goto v___jp_475_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_545_, v_binderInfo_545_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_inc(v_binderName_542_);
lean_dec_ref_known(v_e_424_, 3);
v___x_558_ = l_Lean_Expr_lam___override(v_binderName_542_, v_fst_547_, v_fst_552_, v_binderInfo_545_);
v_fst_476_ = v___x_558_;
v_snd_477_ = v_snd_553_;
goto v___jp_475_;
}
else
{
lean_dec(v_fst_552_);
lean_dec(v_fst_547_);
v_fst_476_ = v_e_424_;
v_snd_477_ = v_snd_553_;
goto v___jp_475_;
}
}
}
}
case 7:
{
lean_object* v_binderName_565_; lean_object* v_binderType_566_; lean_object* v_body_567_; uint8_t v_binderInfo_568_; lean_object* v___x_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_fst_575_; lean_object* v_snd_576_; uint8_t v___y_578_; size_t v___x_582_; size_t v___x_583_; uint8_t v___x_584_; 
v_binderName_565_ = lean_ctor_get(v_e_424_, 0);
v_binderType_566_ = lean_ctor_get(v_e_424_, 1);
v_body_567_ = lean_ctor_get(v_e_424_, 2);
v_binderInfo_568_ = lean_ctor_get_uint8(v_e_424_, sizeof(void*)*3 + 8);
lean_inc(v_offset_425_);
lean_inc_ref(v_binderType_566_);
v___x_569_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_binderType_566_, v_offset_425_, v_a_426_);
v_fst_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_fst_570_);
v_snd_571_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_snd_571_);
lean_dec_ref(v___x_569_);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_offset_425_, v___x_572_);
lean_dec(v_offset_425_);
lean_inc_ref(v_body_567_);
v___x_574_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_body_567_, v___x_573_, v_snd_571_);
v_fst_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_fst_575_);
v_snd_576_ = lean_ctor_get(v___x_574_, 1);
lean_inc(v_snd_576_);
lean_dec_ref(v___x_574_);
v___x_582_ = lean_ptr_addr(v_binderType_566_);
v___x_583_ = lean_ptr_addr(v_fst_570_);
v___x_584_ = lean_usize_dec_eq(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
v___y_578_ = v___x_584_;
goto v___jp_577_;
}
else
{
size_t v___x_585_; size_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_ptr_addr(v_body_567_);
v___x_586_ = lean_ptr_addr(v_fst_575_);
v___x_587_ = lean_usize_dec_eq(v___x_585_, v___x_586_);
v___y_578_ = v___x_587_;
goto v___jp_577_;
}
v___jp_577_:
{
if (v___y_578_ == 0)
{
lean_object* v___x_579_; 
lean_inc(v_binderName_565_);
lean_dec_ref_known(v_e_424_, 3);
v___x_579_ = l_Lean_Expr_forallE___override(v_binderName_565_, v_fst_570_, v_fst_575_, v_binderInfo_568_);
v_fst_476_ = v___x_579_;
v_snd_477_ = v_snd_576_;
goto v___jp_475_;
}
else
{
uint8_t v___x_580_; 
v___x_580_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_568_, v_binderInfo_568_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_inc(v_binderName_565_);
lean_dec_ref_known(v_e_424_, 3);
v___x_581_ = l_Lean_Expr_forallE___override(v_binderName_565_, v_fst_570_, v_fst_575_, v_binderInfo_568_);
v_fst_476_ = v___x_581_;
v_snd_477_ = v_snd_576_;
goto v___jp_475_;
}
else
{
lean_dec(v_fst_575_);
lean_dec(v_fst_570_);
v_fst_476_ = v_e_424_;
v_snd_477_ = v_snd_576_;
goto v___jp_475_;
}
}
}
}
case 8:
{
lean_object* v_declName_588_; lean_object* v_type_589_; lean_object* v_value_590_; lean_object* v_body_591_; uint8_t v_nondep_592_; lean_object* v___x_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_596_; lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_fst_602_; lean_object* v_snd_603_; uint8_t v___y_605_; size_t v___x_611_; size_t v___x_612_; uint8_t v___x_613_; 
v_declName_588_ = lean_ctor_get(v_e_424_, 0);
v_type_589_ = lean_ctor_get(v_e_424_, 1);
v_value_590_ = lean_ctor_get(v_e_424_, 2);
v_body_591_ = lean_ctor_get(v_e_424_, 3);
v_nondep_592_ = lean_ctor_get_uint8(v_e_424_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_425_, 2);
lean_inc_ref(v_type_589_);
v___x_593_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_type_589_, v_offset_425_, v_a_426_);
v_fst_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v___x_593_, 1);
lean_inc(v_snd_595_);
lean_dec_ref(v___x_593_);
lean_inc_ref(v_value_590_);
v___x_596_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_value_590_, v_offset_425_, v_snd_595_);
v_fst_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_fst_597_);
v_snd_598_ = lean_ctor_get(v___x_596_, 1);
lean_inc(v_snd_598_);
lean_dec_ref(v___x_596_);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_add(v_offset_425_, v___x_599_);
lean_dec(v_offset_425_);
lean_inc_ref(v_body_591_);
v___x_601_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_body_591_, v___x_600_, v_snd_598_);
v_fst_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_fst_602_);
v_snd_603_ = lean_ctor_get(v___x_601_, 1);
lean_inc(v_snd_603_);
lean_dec_ref(v___x_601_);
v___x_611_ = lean_ptr_addr(v_type_589_);
v___x_612_ = lean_ptr_addr(v_fst_594_);
v___x_613_ = lean_usize_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
v___y_605_ = v___x_613_;
goto v___jp_604_;
}
else
{
size_t v___x_614_; size_t v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_ptr_addr(v_value_590_);
v___x_615_ = lean_ptr_addr(v_fst_597_);
v___x_616_ = lean_usize_dec_eq(v___x_614_, v___x_615_);
v___y_605_ = v___x_616_;
goto v___jp_604_;
}
v___jp_604_:
{
if (v___y_605_ == 0)
{
lean_object* v___x_606_; 
lean_inc(v_declName_588_);
lean_dec_ref_known(v_e_424_, 4);
v___x_606_ = l_Lean_Expr_letE___override(v_declName_588_, v_fst_594_, v_fst_597_, v_fst_602_, v_nondep_592_);
v_fst_476_ = v___x_606_;
v_snd_477_ = v_snd_603_;
goto v___jp_475_;
}
else
{
size_t v___x_607_; size_t v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_ptr_addr(v_body_591_);
v___x_608_ = lean_ptr_addr(v_fst_602_);
v___x_609_ = lean_usize_dec_eq(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
lean_inc(v_declName_588_);
lean_dec_ref_known(v_e_424_, 4);
v___x_610_ = l_Lean_Expr_letE___override(v_declName_588_, v_fst_594_, v_fst_597_, v_fst_602_, v_nondep_592_);
v_fst_476_ = v___x_610_;
v_snd_477_ = v_snd_603_;
goto v___jp_475_;
}
else
{
lean_dec(v_fst_602_);
lean_dec(v_fst_597_);
lean_dec(v_fst_594_);
v_fst_476_ = v_e_424_;
v_snd_477_ = v_snd_603_;
goto v___jp_475_;
}
}
}
}
case 9:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec_ref_known(v_e_424_, 1);
lean_dec(v_offset_425_);
v___x_617_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_618_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v___x_617_, v_a_426_);
v___y_511_ = v___x_618_;
goto v___jp_510_;
}
case 10:
{
lean_object* v_data_619_; lean_object* v_expr_620_; lean_object* v___x_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; size_t v___x_624_; size_t v___x_625_; uint8_t v___x_626_; 
v_data_619_ = lean_ctor_get(v_e_424_, 0);
v_expr_620_ = lean_ctor_get(v_e_424_, 1);
lean_inc_ref(v_expr_620_);
v___x_621_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_expr_620_, v_offset_425_, v_a_426_);
v_fst_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v___x_621_, 1);
lean_inc(v_snd_623_);
lean_dec_ref(v___x_621_);
v___x_624_ = lean_ptr_addr(v_expr_620_);
v___x_625_ = lean_ptr_addr(v_fst_622_);
v___x_626_ = lean_usize_dec_eq(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_inc(v_data_619_);
lean_dec_ref_known(v_e_424_, 2);
v___x_627_ = l_Lean_Expr_mdata___override(v_data_619_, v_fst_622_);
v_fst_476_ = v___x_627_;
v_snd_477_ = v_snd_623_;
goto v___jp_475_;
}
else
{
lean_dec(v_fst_622_);
v_fst_476_ = v_e_424_;
v_snd_477_ = v_snd_623_;
goto v___jp_475_;
}
}
default: 
{
lean_object* v_typeName_628_; lean_object* v_idx_629_; lean_object* v_struct_630_; lean_object* v___x_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; size_t v___x_634_; size_t v___x_635_; uint8_t v___x_636_; 
v_typeName_628_ = lean_ctor_get(v_e_424_, 0);
v_idx_629_ = lean_ctor_get(v_e_424_, 1);
v_struct_630_ = lean_ctor_get(v_e_424_, 2);
lean_inc_ref(v_struct_630_);
v___x_631_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_421_, v_stop_422_, v_args_423_, v_struct_630_, v_offset_425_, v_a_426_);
v_fst_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v___x_631_, 1);
lean_inc(v_snd_633_);
lean_dec_ref(v___x_631_);
v___x_634_ = lean_ptr_addr(v_struct_630_);
v___x_635_ = lean_ptr_addr(v_fst_632_);
v___x_636_ = lean_usize_dec_eq(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_inc(v_idx_629_);
lean_inc(v_typeName_628_);
lean_dec_ref_known(v_e_424_, 3);
v___x_637_ = l_Lean_Expr_proj___override(v_typeName_628_, v_idx_629_, v_fst_632_);
v_fst_476_ = v___x_637_;
v_snd_477_ = v_snd_633_;
goto v___jp_475_;
}
else
{
lean_dec(v_fst_632_);
v_fst_476_ = v_e_424_;
v_snd_477_ = v_snd_633_;
goto v___jp_475_;
}
}
}
}
else
{
lean_object* v_val_638_; lean_object* v___x_639_; 
lean_dec_ref_known(v___x_429_, 2);
lean_dec(v_offset_425_);
lean_dec_ref(v_e_424_);
v_val_638_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v___x_514_, 1);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_val_638_);
lean_ctor_set(v___x_639_, 1, v_a_426_);
return v___x_639_;
}
v___jp_430_:
{
lean_object* v_size_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_size_434_ = lean_ctor_get(v___y_431_, 0);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_add(v_size_434_, v___x_435_);
lean_inc_ref(v___y_432_);
v___x_437_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_431_, v___x_436_, v_i_433_, v___x_429_, v___y_432_);
lean_dec(v_i_433_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___y_432_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
v___jp_439_:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v___y_441_, v___x_429_);
switch(lean_obj_tag(v___x_442_))
{
case 0:
{
lean_object* v_index_443_; lean_object* v_size_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_index_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_442_, 3);
v_size_444_ = lean_ctor_get(v___y_441_, 0);
lean_inc(v_size_444_);
lean_inc_ref(v___y_440_);
v___x_445_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_441_, v_size_444_, v_index_443_, v___x_429_, v___y_440_);
lean_dec(v_index_443_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___y_440_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
case 1:
{
lean_object* v_index_447_; 
v_index_447_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_index_447_);
lean_dec_ref_known(v___x_442_, 1);
v___y_431_ = v___y_441_;
v___y_432_ = v___y_440_;
v_i_433_ = v_index_447_;
goto v___jp_430_;
}
default: 
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_441_, v___x_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_index_450_; 
v_index_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_index_450_);
lean_dec_ref_known(v___x_449_, 1);
v___y_431_ = v___y_441_;
v___y_432_ = v___y_440_;
v_i_433_ = v_index_450_;
goto v___jp_430_;
}
else
{
lean_object* v___x_451_; 
lean_dec_ref_known(v___x_429_, 2);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_440_);
lean_ctor_set(v___x_451_, 1, v___y_441_);
return v___x_451_;
}
}
}
}
v___jp_452_:
{
lean_object* v_size_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_size_456_ = lean_ctor_get(v___y_453_, 0);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_size_456_, v___x_457_);
lean_inc_ref(v___y_454_);
v___x_459_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_453_, v___x_458_, v_i_455_, v___x_429_, v___y_454_);
lean_dec(v_i_455_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___y_454_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
return v___x_460_;
}
v___jp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v___y_463_);
lean_dec_ref(v___y_463_);
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v___x_464_, v___x_429_);
switch(lean_obj_tag(v___x_465_))
{
case 0:
{
lean_object* v_index_466_; lean_object* v_size_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_index_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_index_466_);
lean_dec_ref_known(v___x_465_, 3);
v_size_467_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_size_467_);
lean_inc_ref(v___y_462_);
v___x_468_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_464_, v_size_467_, v_index_466_, v___x_429_, v___y_462_);
lean_dec(v_index_466_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___y_462_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
return v___x_469_;
}
case 1:
{
lean_object* v_index_470_; 
v_index_470_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_index_470_);
lean_dec_ref_known(v___x_465_, 1);
v___y_453_ = v___x_464_;
v___y_454_ = v___y_462_;
v_i_455_ = v_index_470_;
goto v___jp_452_;
}
default: 
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_464_, v___x_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_index_473_; 
v_index_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_index_473_);
lean_dec_ref_known(v___x_472_, 1);
v___y_453_ = v___x_464_;
v___y_454_ = v___y_462_;
v_i_455_ = v_index_473_;
goto v___jp_452_;
}
else
{
lean_object* v___x_474_; 
lean_dec_ref_known(v___x_429_, 2);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___y_462_);
lean_ctor_set(v___x_474_, 1, v___x_464_);
return v___x_474_;
}
}
}
}
v___jp_475_:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_snd_477_, v___x_429_);
switch(lean_obj_tag(v___x_478_))
{
case 0:
{
lean_object* v_index_479_; lean_object* v_size_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_index_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_index_479_);
lean_dec_ref_known(v___x_478_, 3);
v_size_480_ = lean_ctor_get(v_snd_477_, 0);
lean_inc(v_size_480_);
lean_inc_ref(v_fst_476_);
v___x_481_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_477_, v_size_480_, v_index_479_, v___x_429_, v_fst_476_);
lean_dec(v_index_479_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_fst_476_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
return v___x_482_;
}
case 1:
{
lean_object* v_index_483_; lean_object* v_size_484_; lean_object* v_keyArray_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_index_483_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_index_483_);
lean_dec_ref_known(v___x_478_, 1);
v_size_484_ = lean_ctor_get(v_snd_477_, 0);
v_keyArray_485_ = lean_ctor_get(v_snd_477_, 1);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_size_484_, v___x_486_);
v___x_488_ = lean_array_get_size(v_keyArray_485_);
v___x_489_ = lean_nat_dec_lt(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v___x_487_);
lean_dec(v_index_483_);
v___y_462_ = v_fst_476_;
v___y_463_ = v_snd_477_;
goto v___jp_461_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_490_ = lean_unsigned_to_nat(4u);
v___x_491_ = lean_nat_mul(v___x_487_, v___x_490_);
v___x_492_ = lean_unsigned_to_nat(3u);
v___x_493_ = lean_nat_mul(v___x_488_, v___x_492_);
v___x_494_ = lean_nat_dec_le(v___x_491_, v___x_493_);
lean_dec(v___x_493_);
lean_dec(v___x_491_);
if (v___x_494_ == 0)
{
lean_dec(v___x_487_);
lean_dec(v_index_483_);
v___y_462_ = v_fst_476_;
v___y_463_ = v_snd_477_;
goto v___jp_461_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc_ref(v_fst_476_);
v___x_495_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_477_, v___x_487_, v_index_483_, v___x_429_, v_fst_476_);
lean_dec(v_index_483_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v_fst_476_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
return v___x_496_;
}
}
}
default: 
{
lean_object* v_size_497_; lean_object* v_keyArray_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_size_497_ = lean_ctor_get(v_snd_477_, 0);
v_keyArray_498_ = lean_ctor_get(v_snd_477_, 1);
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_size_497_, v___x_499_);
v___x_501_ = lean_array_get_size(v_keyArray_498_);
v___x_502_ = lean_nat_dec_lt(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v___x_500_);
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v_snd_477_);
lean_dec_ref(v_snd_477_);
v___y_440_ = v_fst_476_;
v___y_441_ = v___x_503_;
goto v___jp_439_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_504_ = lean_unsigned_to_nat(4u);
v___x_505_ = lean_nat_mul(v___x_500_, v___x_504_);
lean_dec(v___x_500_);
v___x_506_ = lean_unsigned_to_nat(3u);
v___x_507_ = lean_nat_mul(v___x_501_, v___x_506_);
v___x_508_ = lean_nat_dec_le(v___x_505_, v___x_507_);
lean_dec(v___x_507_);
lean_dec(v___x_505_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v_snd_477_);
lean_dec_ref(v_snd_477_);
v___y_440_ = v_fst_476_;
v___y_441_ = v___x_509_;
goto v___jp_439_;
}
else
{
v___y_440_ = v_fst_476_;
v___y_441_ = v_snd_477_;
goto v___jp_439_;
}
}
}
}
}
v___jp_510_:
{
lean_object* v_fst_512_; lean_object* v_snd_513_; 
v_fst_512_ = lean_ctor_get(v___y_511_, 0);
lean_inc(v_fst_512_);
v_snd_513_ = lean_ctor_get(v___y_511_, 1);
lean_inc(v_snd_513_);
lean_dec_ref(v___y_511_);
v_fst_476_ = v_fst_512_;
v_snd_477_ = v_snd_513_;
goto v___jp_475_;
}
}
else
{
lean_object* v___x_640_; 
lean_dec(v_offset_425_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v_e_424_);
lean_ctor_set(v___x_640_, 1, v_a_426_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__5(lean_object* v_start_641_, lean_object* v_stop_642_, lean_object* v_args_643_, lean_object* v_offset_644_, size_t v_sz_645_, size_t v_i_646_, lean_object* v_bs_647_, lean_object* v___y_648_){
_start:
{
uint8_t v___x_649_; 
v___x_649_ = lean_usize_dec_lt(v_i_646_, v_sz_645_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec(v_offset_644_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_bs_647_);
lean_ctor_set(v___x_650_, 1, v___y_648_);
return v___x_650_;
}
else
{
lean_object* v_v_651_; lean_object* v___x_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_655_; lean_object* v_bs_x27_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v_v_651_ = lean_array_uget_borrowed(v_bs_647_, v_i_646_);
lean_inc(v_offset_644_);
lean_inc(v_v_651_);
v___x_652_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_641_, v_stop_642_, v_args_643_, v_v_651_, v_offset_644_, v___y_648_);
v_fst_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_snd_654_);
lean_dec_ref(v___x_652_);
v___x_655_ = lean_unsigned_to_nat(0u);
v_bs_x27_656_ = lean_array_uset(v_bs_647_, v_i_646_, v___x_655_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_add(v_i_646_, v___x_657_);
v___x_659_ = lean_array_uset(v_bs_x27_656_, v_i_646_, v_fst_653_);
v_i_646_ = v___x_658_;
v_bs_647_ = v___x_659_;
v___y_648_ = v_snd_654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__5___boxed(lean_object* v_start_661_, lean_object* v_stop_662_, lean_object* v_args_663_, lean_object* v_offset_664_, lean_object* v_sz_665_, lean_object* v_i_666_, lean_object* v_bs_667_, lean_object* v___y_668_){
_start:
{
size_t v_sz_boxed_669_; size_t v_i_boxed_670_; lean_object* v_res_671_; 
v_sz_boxed_669_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_670_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__5(v_start_661_, v_stop_662_, v_args_663_, v_offset_664_, v_sz_boxed_669_, v_i_boxed_670_, v_bs_667_, v___y_668_);
lean_dec_ref(v_args_663_);
lean_dec(v_stop_662_);
lean_dec(v_start_661_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp___boxed(lean_object* v_start_672_, lean_object* v_stop_673_, lean_object* v_args_674_, lean_object* v_e_675_, lean_object* v_f_676_, lean_object* v_a_677_, lean_object* v_offset_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp(v_start_672_, v_stop_673_, v_args_674_, v_e_675_, v_f_676_, v_a_677_, v_offset_678_, v_a_679_);
lean_dec_ref(v_args_674_);
lean_dec(v_stop_673_);
lean_dec(v_start_672_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta___boxed(lean_object* v_start_681_, lean_object* v_stop_682_, lean_object* v_args_683_, lean_object* v_e_684_, lean_object* v_offset_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta(v_start_681_, v_stop_682_, v_args_683_, v_e_684_, v_offset_685_, v_a_686_);
lean_dec_ref(v_args_683_);
lean_dec(v_stop_682_);
lean_dec(v_start_681_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_688_, lean_object* v_stop_689_, lean_object* v_args_690_, lean_object* v_e_691_, lean_object* v_offset_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_688_, v_stop_689_, v_args_690_, v_e_691_, v_offset_692_, v_a_693_);
lean_dec_ref(v_args_690_);
lean_dec(v_stop_689_);
lean_dec(v_start_688_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(lean_object* v_00_u03b2_695_, lean_object* v_m_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___redArg(v_m_696_, v_a_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0___boxed(lean_object* v_00_u03b2_699_, lean_object* v_m_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0(v_00_u03b2_699_, v_m_700_, v_a_701_);
lean_dec_ref(v_a_701_);
lean_dec_ref(v_m_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(lean_object* v_00_u03b2_703_, lean_object* v_m_704_, lean_object* v_query_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___redArg(v_m_704_, v_query_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1___boxed(lean_object* v_00_u03b2_707_, lean_object* v_m_708_, lean_object* v_query_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1(v_00_u03b2_707_, v_m_708_, v_query_709_);
lean_dec_ref(v_query_709_);
lean_dec_ref(v_m_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2(lean_object* v_00_u03b2_711_, lean_object* v_m_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___redArg(v_m_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2___boxed(lean_object* v_00_u03b2_714_, lean_object* v_m_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2(v_00_u03b2_714_, v_m_715_);
lean_dec_ref(v_m_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(lean_object* v_00_u03b2_717_, lean_object* v_m_718_, lean_object* v_query_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___redArg(v_m_718_, v_query_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0___boxed(lean_object* v_00_u03b2_721_, lean_object* v_m_722_, lean_object* v_query_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__0_spec__0(v_00_u03b2_721_, v_m_722_, v_query_723_);
lean_dec_ref(v_query_723_);
lean_dec_ref(v_m_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(lean_object* v_00_u03b2_725_, lean_object* v_m_726_, lean_object* v_query_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___redArg(v_m_726_, v_query_727_, v_x_728_, v_x_729_, v_x_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2___boxed(lean_object* v_00_u03b2_733_, lean_object* v_m_734_, lean_object* v_query_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__1_spec__2(v_00_u03b2_733_, v_m_734_, v_query_735_, v_x_736_, v_x_737_, v_x_738_, v_x_739_);
lean_dec_ref(v_query_735_);
lean_dec_ref(v_m_734_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4(lean_object* v_00_u03b2_741_, lean_object* v_init_742_, lean_object* v_b_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___redArg(v_init_742_, v_b_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4___boxed(lean_object* v_00_u03b2_745_, lean_object* v_init_746_, lean_object* v_b_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4(v_00_u03b2_745_, v_init_746_, v_b_747_);
lean_dec_ref(v_b_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9(lean_object* v_00_u03b2_749_, lean_object* v_b_750_, lean_object* v_acc_751_, lean_object* v_i_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___redArg(v_b_750_, v_acc_751_, v_i_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b2_754_, lean_object* v_b_755_, lean_object* v_acc_756_, lean_object* v_i_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitWithoutBeta_spec__2_spec__4_spec__9(v_00_u03b2_754_, v_b_755_, v_acc_756_, v_i_757_);
lean_dec_ref(v_b_755_);
return v_res_758_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_as_759_, size_t v_i_760_, size_t v_stop_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = lean_usize_dec_eq(v_i_760_, v_stop_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_763_ = lean_array_uget_borrowed(v_as_759_, v_i_760_);
v___x_764_ = l_Lean_Expr_consumeMData(v___x_763_);
v___x_765_ = l_Lean_Expr_isLambda(v___x_764_);
lean_dec_ref(v___x_764_);
if (v___x_765_ == 0)
{
size_t v___x_766_; size_t v___x_767_; 
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_760_, v___x_766_);
v_i_760_ = v___x_767_;
goto _start;
}
else
{
return v___x_765_;
}
}
else
{
uint8_t v___x_769_; 
v___x_769_ = 0;
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0___boxed(lean_object* v_as_770_, lean_object* v_i_771_, lean_object* v_stop_772_){
_start:
{
size_t v_i_boxed_773_; size_t v_stop_boxed_774_; uint8_t v_res_775_; lean_object* v_r_776_; 
v_i_boxed_773_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_stop_boxed_774_ = lean_unbox_usize(v_stop_772_);
lean_dec(v_stop_772_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_as_770_, v_i_boxed_773_, v_stop_boxed_774_);
lean_dec_ref(v_as_770_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__0(void){
_start:
{
lean_object* v_cellCount_777_; lean_object* v___x_778_; 
v_cellCount_777_ = lean_unsigned_to_nat(16u);
v___x_778_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1(void){
_start:
{
lean_object* v_cellCount_779_; lean_object* v___x_780_; 
v_cellCount_779_ = lean_unsigned_to_nat(16u);
v___x_780_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__2(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__1, &l_Lean_Expr_instantiateBetaRevRange___closed__1_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__1);
v___x_782_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__0, &l_Lean_Expr_instantiateBetaRevRange___closed__0_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__0);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
lean_ctor_set(v___x_784_, 2, v___x_781_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__5(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_787_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__4));
v___x_788_ = lean_unsigned_to_nat(4u);
v___x_789_ = lean_unsigned_to_nat(39u);
v___x_790_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__3));
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_792_ = l_mkPanicMessageWithDecl(v___x_791_, v___x_790_, v___x_789_, v___x_788_, v___x_787_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_793_, lean_object* v_start_794_, lean_object* v_stop_795_, lean_object* v_args_796_){
_start:
{
lean_object* v___y_798_; uint8_t v___y_810_; uint8_t v___x_817_; 
v___x_817_ = l_Lean_Expr_hasLooseBVars(v_e_793_);
if (v___x_817_ == 0)
{
v___y_810_ = v___x_817_;
goto v___jp_809_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = lean_nat_dec_lt(v_start_794_, v_stop_795_);
v___y_810_ = v___x_818_;
goto v___jp_809_;
}
v___jp_797_:
{
uint8_t v___x_799_; 
v___x_799_ = lean_nat_dec_lt(v_start_794_, v___y_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec(v___y_798_);
v___x_800_ = lean_expr_instantiate_rev_range(v_e_793_, v_start_794_, v_stop_795_, v_args_796_);
lean_dec(v_stop_795_);
lean_dec_ref(v_e_793_);
return v___x_800_;
}
else
{
size_t v___x_801_; size_t v___x_802_; uint8_t v___x_803_; 
v___x_801_ = lean_usize_of_nat(v_start_794_);
v___x_802_ = lean_usize_of_nat(v___y_798_);
lean_dec(v___y_798_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v_args_796_, v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_expr_instantiate_rev_range(v_e_793_, v_start_794_, v_stop_795_, v_args_796_);
lean_dec(v_stop_795_);
lean_dec_ref(v_e_793_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_fst_808_; 
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__2, &l_Lean_Expr_instantiateBetaRevRange___closed__2_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__2);
v___x_807_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_794_, v_stop_795_, v_args_796_, v_e_793_, v___x_805_, v___x_806_);
lean_dec(v_stop_795_);
v_fst_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_fst_808_);
lean_dec_ref(v___x_807_);
return v_fst_808_;
}
}
}
v___jp_809_:
{
if (v___y_810_ == 0)
{
lean_dec(v_stop_795_);
return v_e_793_;
}
else
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_array_get_size(v_args_796_);
v___x_812_ = lean_nat_dec_le(v_stop_795_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_stop_795_);
lean_dec_ref(v_e_793_);
v___x_813_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__5, &l_Lean_Expr_instantiateBetaRevRange___closed__5_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__5);
v___x_814_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visitApp_spec__7(v___x_813_);
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = lean_nat_dec_lt(v_start_794_, v_stop_795_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
v___x_816_ = lean_expr_instantiate_rev_range(v_e_793_, v_start_794_, v_stop_795_, v_args_796_);
lean_dec(v_stop_795_);
lean_dec_ref(v_e_793_);
return v___x_816_;
}
else
{
if (v___x_812_ == 0)
{
v___y_798_ = v___x_811_;
goto v___jp_797_;
}
else
{
lean_inc(v_stop_795_);
v___y_798_ = v_stop_795_;
goto v___jp_797_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_819_, lean_object* v_start_820_, lean_object* v_stop_821_, lean_object* v_args_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Expr_instantiateBetaRevRange(v_e_819_, v_start_820_, v_stop_821_, v_args_822_);
lean_dec_ref(v_args_822_);
lean_dec(v_start_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; lean_object* v_env_831_; lean_object* v___x_832_; lean_object* v_mctx_833_; lean_object* v_lctx_834_; lean_object* v_options_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_830_ = lean_st_ref_get(v___y_828_);
v_env_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc_ref(v_env_831_);
lean_dec(v___x_830_);
v___x_832_ = lean_st_ref_get(v___y_826_);
v_mctx_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc_ref(v_mctx_833_);
lean_dec(v___x_832_);
v_lctx_834_ = lean_ctor_get(v___y_825_, 2);
v_options_835_ = lean_ctor_get(v___y_827_, 2);
lean_inc_ref(v_options_835_);
lean_inc_ref(v_lctx_834_);
v___x_836_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_836_, 0, v_env_831_);
lean_ctor_set(v___x_836_, 1, v_mctx_833_);
lean_ctor_set(v___x_836_, 2, v_lctx_834_);
lean_ctor_set(v___x_836_, 3, v_options_835_);
v___x_837_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_msgData_824_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_ref_852_; lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_ref_852_ = lean_ctor_get(v___y_849_, 5);
v___x_853_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_inc(v_ref_852_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_ref_852_);
lean_ctor_set(v___x_858_, 1, v_a_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
lean_ctor_set(v___x_856_, 0, v___x_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_869_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_872_ = l_Lean_stringToMessageData(v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_880_ = l_Lean_indentExpr(v_f_873_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_881_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_890_, lean_object* v_f_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_898_, lean_object* v_f_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_898_, v_f_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_906_, lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_914_, lean_object* v_msg_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_914_, v_msg_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_922_, lean_object* v_args_923_, lean_object* v_f_924_, lean_object* v_a_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_a_933_; uint8_t v___x_937_; 
v___x_937_ = lean_nat_dec_lt(v_a_925_, v_upperBound_922_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_dec(v_a_925_);
lean_dec_ref(v_f_924_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_b_926_);
return v___x_938_;
}
else
{
lean_object* v_fst_939_; 
v_fst_939_ = lean_ctor_get(v_b_926_, 0);
lean_inc(v_fst_939_);
if (lean_obj_tag(v_fst_939_) == 7)
{
lean_object* v_snd_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_snd_940_ = lean_ctor_get(v_b_926_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_b_926_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_b_926_, 0);
lean_dec(v_unused_949_);
v___x_942_ = v_b_926_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_snd_940_);
lean_dec(v_b_926_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_body_944_; lean_object* v___x_946_; 
v_body_944_ = lean_ctor_get(v_fst_939_, 2);
lean_inc_ref(v_body_944_);
lean_dec_ref_known(v_fst_939_, 3);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_body_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_body_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_snd_940_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
v_a_933_ = v___x_946_;
goto v___jp_932_;
}
}
}
else
{
lean_object* v_snd_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_985_; 
v_snd_950_ = lean_ctor_get(v_b_926_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_b_926_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; 
v_unused_986_ = lean_ctor_get(v_b_926_, 0);
lean_dec(v_unused_986_);
v___x_952_ = v_b_926_;
v_isShared_953_ = v_isSharedCheck_985_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_snd_950_);
lean_dec(v_b_926_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_985_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_inc(v_a_925_);
lean_inc(v_fst_939_);
v___x_954_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_939_, v_snd_950_, v_a_925_, v_args_923_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
v___x_955_ = lean_whnf(v___x_954_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
if (lean_obj_tag(v_a_956_) == 7)
{
lean_object* v_body_957_; lean_object* v___x_959_; 
lean_dec(v_snd_950_);
lean_dec(v_fst_939_);
v_body_957_ = lean_ctor_get(v_a_956_, 2);
lean_inc_ref(v_body_957_);
lean_dec_ref_known(v_a_956_, 3);
lean_inc(v_a_925_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_a_925_);
lean_ctor_set(v___x_952_, 0, v_body_957_);
v___x_959_ = v___x_952_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_body_957_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_a_925_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v_a_933_ = v___x_959_;
goto v___jp_932_;
}
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_a_956_);
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_a_925_, v___x_962_);
lean_inc_ref(v_f_924_);
v___x_964_ = l_Lean_mkAppRange(v_f_924_, v___x_961_, v___x_963_, v_args_923_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_964_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v___x_967_; 
lean_dec_ref_known(v___x_965_, 1);
if (v_isShared_953_ == 0)
{
v___x_967_ = v___x_952_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_fst_939_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_snd_950_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
v_a_933_ = v___x_967_;
goto v___jp_932_;
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
lean_dec(v_fst_939_);
lean_dec(v_a_925_);
lean_dec_ref(v_f_924_);
v_a_969_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_965_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_965_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
lean_dec(v_fst_939_);
lean_dec(v_a_925_);
lean_dec_ref(v_f_924_);
v_a_977_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_955_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_955_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
v___jp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_a_925_, v___x_934_);
lean_dec(v_a_925_);
v_a_925_ = v___x_935_;
v_b_926_ = v_a_933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_987_, lean_object* v_args_988_, lean_object* v_f_989_, lean_object* v_a_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_987_, v_args_988_, v_f_989_, v_a_990_, v_b_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_args_988_);
lean_dec(v_upperBound_987_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_998_, lean_object* v_args_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; 
lean_inc(v_a_1003_);
lean_inc_ref(v_a_1002_);
lean_inc(v_a_1001_);
lean_inc_ref(v_a_1000_);
lean_inc_ref(v_f_998_);
v___x_1005_ = lean_infer_type(v_f_998_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_array_get_size(v_args_999_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_a_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_1007_, v_args_999_, v_f_998_, v___x_1008_, v___x_1009_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1021_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v_fst_1015_ = lean_ctor_get(v_a_1011_, 0);
lean_inc(v_fst_1015_);
v_snd_1016_ = lean_ctor_get(v_a_1011_, 1);
lean_inc(v_snd_1016_);
lean_dec(v_a_1011_);
v___x_1017_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_1015_, v_snd_1016_, v___x_1007_, v_args_999_);
lean_dec(v_snd_1016_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1010_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1010_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_dec_ref(v_f_998_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_1030_, lean_object* v_args_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_1030_, v_args_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec_ref(v_args_1031_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_1038_, lean_object* v_args_1039_, lean_object* v_f_1040_, lean_object* v_inst_1041_, lean_object* v_R_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_, lean_object* v_c_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_1038_, v_args_1039_, v_f_1040_, v_a_1043_, v_b_1044_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_1052_, lean_object* v_args_1053_, lean_object* v_f_1054_, lean_object* v_inst_1055_, lean_object* v_R_1056_, lean_object* v_a_1057_, lean_object* v_b_1058_, lean_object* v_c_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_1052_, v_args_1053_, v_f_1054_, v_inst_1055_, v_R_1056_, v_a_1057_, v_b_1058_, v_c_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_args_1053_);
lean_dec(v_upperBound_1052_);
return v_res_1065_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_1069_, lean_object* v_us_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1076_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_1077_ = l_Lean_mkConst(v_constName_1069_, v_us_1070_);
v___x_1078_ = l_Lean_MessageData_ofExpr(v___x_1077_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1076_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1079_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_1081_, lean_object* v_us_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_1081_, v_us_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_1089_, lean_object* v_constName_1090_, lean_object* v_us_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_1090_, v_us_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_1098_, lean_object* v_constName_1099_, lean_object* v_us_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_1098_, v_constName_1099_, v_us_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1107_, lean_object* v_msg_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_fileName_1114_; lean_object* v_fileMap_1115_; lean_object* v_options_1116_; lean_object* v_currRecDepth_1117_; lean_object* v_maxRecDepth_1118_; lean_object* v_ref_1119_; lean_object* v_currNamespace_1120_; lean_object* v_openDecls_1121_; lean_object* v_initHeartbeats_1122_; lean_object* v_maxHeartbeats_1123_; lean_object* v_quotContext_1124_; lean_object* v_currMacroScope_1125_; uint8_t v_diag_1126_; lean_object* v_cancelTk_x3f_1127_; uint8_t v_suppressElabErrors_1128_; lean_object* v_inheritedTraceOptions_1129_; lean_object* v_ref_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_fileName_1114_ = lean_ctor_get(v___y_1111_, 0);
v_fileMap_1115_ = lean_ctor_get(v___y_1111_, 1);
v_options_1116_ = lean_ctor_get(v___y_1111_, 2);
v_currRecDepth_1117_ = lean_ctor_get(v___y_1111_, 3);
v_maxRecDepth_1118_ = lean_ctor_get(v___y_1111_, 4);
v_ref_1119_ = lean_ctor_get(v___y_1111_, 5);
v_currNamespace_1120_ = lean_ctor_get(v___y_1111_, 6);
v_openDecls_1121_ = lean_ctor_get(v___y_1111_, 7);
v_initHeartbeats_1122_ = lean_ctor_get(v___y_1111_, 8);
v_maxHeartbeats_1123_ = lean_ctor_get(v___y_1111_, 9);
v_quotContext_1124_ = lean_ctor_get(v___y_1111_, 10);
v_currMacroScope_1125_ = lean_ctor_get(v___y_1111_, 11);
v_diag_1126_ = lean_ctor_get_uint8(v___y_1111_, sizeof(void*)*14);
v_cancelTk_x3f_1127_ = lean_ctor_get(v___y_1111_, 12);
v_suppressElabErrors_1128_ = lean_ctor_get_uint8(v___y_1111_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1129_ = lean_ctor_get(v___y_1111_, 13);
v_ref_1130_ = l_Lean_replaceRef(v_ref_1107_, v_ref_1119_);
lean_inc_ref(v_inheritedTraceOptions_1129_);
lean_inc(v_cancelTk_x3f_1127_);
lean_inc(v_currMacroScope_1125_);
lean_inc(v_quotContext_1124_);
lean_inc(v_maxHeartbeats_1123_);
lean_inc(v_initHeartbeats_1122_);
lean_inc(v_openDecls_1121_);
lean_inc(v_currNamespace_1120_);
lean_inc(v_maxRecDepth_1118_);
lean_inc(v_currRecDepth_1117_);
lean_inc_ref(v_options_1116_);
lean_inc_ref(v_fileMap_1115_);
lean_inc_ref(v_fileName_1114_);
v___x_1131_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1131_, 0, v_fileName_1114_);
lean_ctor_set(v___x_1131_, 1, v_fileMap_1115_);
lean_ctor_set(v___x_1131_, 2, v_options_1116_);
lean_ctor_set(v___x_1131_, 3, v_currRecDepth_1117_);
lean_ctor_set(v___x_1131_, 4, v_maxRecDepth_1118_);
lean_ctor_set(v___x_1131_, 5, v_ref_1130_);
lean_ctor_set(v___x_1131_, 6, v_currNamespace_1120_);
lean_ctor_set(v___x_1131_, 7, v_openDecls_1121_);
lean_ctor_set(v___x_1131_, 8, v_initHeartbeats_1122_);
lean_ctor_set(v___x_1131_, 9, v_maxHeartbeats_1123_);
lean_ctor_set(v___x_1131_, 10, v_quotContext_1124_);
lean_ctor_set(v___x_1131_, 11, v_currMacroScope_1125_);
lean_ctor_set(v___x_1131_, 12, v_cancelTk_x3f_1127_);
lean_ctor_set(v___x_1131_, 13, v_inheritedTraceOptions_1129_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*14, v_diag_1126_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*14 + 1, v_suppressElabErrors_1128_);
v___x_1132_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_1108_, v___y_1109_, v___y_1110_, v___x_1131_, v___y_1112_);
lean_dec_ref_known(v___x_1131_, 14);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1133_, lean_object* v_msg_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1133_, v_msg_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v_ref_1133_);
return v_res_1140_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
lean_ctor_set(v___x_1146_, 2, v___x_1145_);
lean_ctor_set(v___x_1146_, 3, v___x_1145_);
lean_ctor_set(v___x_1146_, 4, v___x_1144_);
lean_ctor_set(v___x_1146_, 5, v___x_1144_);
lean_ctor_set(v___x_1146_, 6, v___x_1144_);
lean_ctor_set(v___x_1146_, 7, v___x_1144_);
lean_ctor_set(v___x_1146_, 8, v___x_1144_);
lean_ctor_set(v___x_1146_, 9, v___x_1144_);
lean_ctor_set(v___x_1146_, 10, v___x_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = lean_unsigned_to_nat(32u);
v___x_1148_ = lean_mk_empty_array_with_capacity(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1150_ = ((size_t)5ULL);
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = lean_unsigned_to_nat(32u);
v___x_1153_ = lean_mk_empty_array_with_capacity(v___x_1152_);
v___x_1154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_1155_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
lean_ctor_set(v___x_1155_, 2, v___x_1151_);
lean_ctor_set(v___x_1155_, 3, v___x_1151_);
lean_ctor_set_usize(v___x_1155_, 4, v___x_1150_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_box(1);
v___x_1157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_1159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1157_);
lean_ctor_set(v___x_1159_, 2, v___x_1156_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_1171_ = l_Lean_stringToMessageData(v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_1174_ = l_Lean_stringToMessageData(v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_1177_ = l_Lean_stringToMessageData(v___x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_1180_ = l_Lean_stringToMessageData(v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_1181_, lean_object* v_declHint_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; uint8_t v___x_1187_; 
v___x_1185_ = lean_st_ref_get(v___y_1183_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc_ref(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1187_ = l_Lean_Name_isAnonymous(v_declHint_1182_);
if (v___x_1187_ == 0)
{
uint8_t v_isExporting_1188_; 
v_isExporting_1188_ = lean_ctor_get_uint8(v_env_1186_, sizeof(void*)*8);
if (v_isExporting_1188_ == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v_env_1186_);
lean_dec(v_declHint_1182_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_msg_1181_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
lean_inc_ref(v_env_1186_);
v___x_1190_ = l_Lean_Environment_setExporting(v_env_1186_, v___x_1187_);
lean_inc(v_declHint_1182_);
lean_inc_ref(v___x_1190_);
v___x_1191_ = l_Lean_Environment_contains(v___x_1190_, v_declHint_1182_, v_isExporting_1188_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_env_1186_);
lean_dec(v_declHint_1182_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_msg_1181_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_c_1198_; lean_object* v___x_1199_; 
v___x_1193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_1194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_1195_ = l_Lean_Options_empty;
v___x_1196_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1190_);
lean_ctor_set(v___x_1196_, 1, v___x_1193_);
lean_ctor_set(v___x_1196_, 2, v___x_1194_);
lean_ctor_set(v___x_1196_, 3, v___x_1195_);
lean_inc(v_declHint_1182_);
v___x_1197_ = l_Lean_MessageData_ofConstName(v_declHint_1182_, v___x_1187_);
v_c_1198_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1198_, 0, v___x_1196_);
lean_ctor_set(v_c_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1186_, v_declHint_1182_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec_ref(v_env_1186_);
lean_dec(v_declHint_1182_);
v___x_1200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v_c_1198_);
v___x_1202_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Lean_MessageData_note(v___x_1203_);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_msg_1181_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
else
{
lean_object* v_val_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1242_; 
v_val_1207_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1209_ = v___x_1199_;
v_isShared_1210_ = v_isSharedCheck_1242_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_val_1207_);
lean_dec(v___x_1199_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1242_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_mod_1214_; uint8_t v___x_1215_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Lean_Environment_header(v_env_1186_);
lean_dec_ref(v_env_1186_);
v___x_1213_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1212_);
v_mod_1214_ = lean_array_get(v___x_1211_, v___x_1213_, v_val_1207_);
lean_dec(v_val_1207_);
lean_dec_ref(v___x_1213_);
v___x_1215_ = l_Lean_isPrivateName(v_declHint_1182_);
lean_dec(v_declHint_1182_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_c_1198_);
v___x_1218_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_1219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = l_Lean_MessageData_ofName(v_mod_1214_);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_MessageData_note(v___x_1223_);
v___x_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_msg_1181_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1225_);
v___x_1227_ = v___x_1209_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v_c_1198_);
v___x_1231_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_MessageData_ofName(v_mod_1214_);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = l_Lean_MessageData_note(v___x_1236_);
v___x_1238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_msg_1181_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1238_);
v___x_1240_ = v___x_1209_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1243_; 
lean_dec_ref(v_env_1186_);
lean_dec(v_declHint_1182_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_msg_1181_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_1244_, lean_object* v_declHint_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1244_, v_declHint_1245_, v___y_1246_);
lean_dec(v___y_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_1249_, lean_object* v_declHint_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1266_; 
v___x_1256_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1249_, v_declHint_1250_, v___y_1254_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1261_ = l_Lean_unknownIdentifierMessageTag;
v___x_1262_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1262_);
v___x_1264_ = v___x_1259_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1267_, lean_object* v_declHint_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1267_, v_declHint_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1275_, lean_object* v_msg_1276_, lean_object* v_declHint_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_a_1284_; lean_object* v___x_1285_; 
v___x_1283_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1276_, v_declHint_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1275_, v_a_1284_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1286_, lean_object* v_msg_1287_, lean_object* v_declHint_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1286_, v_msg_1287_, v_declHint_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v_ref_1286_);
return v_res_1294_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1301_, lean_object* v_constName_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1308_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1309_ = 0;
lean_inc(v_constName_1302_);
v___x_1310_ = l_Lean_MessageData_ofConstName(v_constName_1302_, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1308_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1301_, v___x_1313_, v_constName_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1315_, lean_object* v_constName_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1315_, v_constName_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v_ref_1315_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_ref_1329_; lean_object* v___x_1330_; 
v_ref_1329_ = lean_ctor_get(v___y_1326_, 5);
v___x_1330_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1329_, v_constName_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v_env_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1344_ = lean_st_ref_get(v___y_1342_);
v_env_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc_ref(v_env_1345_);
lean_dec(v___x_1344_);
v___x_1346_ = 0;
lean_inc(v_constName_1338_);
v___x_1347_ = l_Lean_Environment_findConstVal_x3f(v_env_1345_, v_constName_1338_, v___x_1346_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1348_;
}
else
{
lean_object* v_val_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_constName_1338_);
v_val_1349_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1347_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_val_1349_);
lean_dec(v___x_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set_tag(v___x_1351_, 0);
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_val_1349_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1364_, lean_object* v_us_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1371_; 
lean_inc(v_c_1364_);
v___x_1371_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1364_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v_levelParams_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v_levelParams_1373_ = lean_ctor_get(v_a_1372_, 1);
v___x_1374_ = l_List_lengthTR___redArg(v_levelParams_1373_);
v___x_1375_ = l_List_lengthTR___redArg(v_us_1365_);
v___x_1376_ = lean_nat_dec_eq(v___x_1374_, v___x_1375_);
lean_dec(v___x_1375_);
lean_dec(v___x_1374_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec(v_a_1372_);
v___x_1377_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1364_, v_us_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; 
lean_dec(v_c_1364_);
v___x_1378_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1372_, v_us_1365_, v_a_1369_);
return v___x_1378_;
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_us_1365_);
lean_dec(v_c_1364_);
v_a_1379_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1371_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1371_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1387_, lean_object* v_us_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1387_, v_us_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1395_, lean_object* v_constName_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_constName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1403_, v_constName_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1411_, lean_object* v_ref_1412_, lean_object* v_constName_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1412_, v_constName_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1420_, lean_object* v_ref_1421_, lean_object* v_constName_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1420_, v_ref_1421_, v_constName_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v_ref_1421_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1429_, lean_object* v_ref_1430_, lean_object* v_msg_1431_, lean_object* v_declHint_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1430_, v_msg_1431_, v_declHint_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_ref_1440_, lean_object* v_msg_1441_, lean_object* v_declHint_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1439_, v_ref_1440_, v_msg_1441_, v_declHint_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v_ref_1440_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1449_, lean_object* v_declHint_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1449_, v_declHint_1450_, v___y_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1457_, lean_object* v_declHint_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1457_, v_declHint_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1465_, lean_object* v_ref_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1466_, v_msg_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1474_, lean_object* v_ref_1475_, lean_object* v_msg_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1474_, v_ref_1475_, v_msg_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v_ref_1475_);
return v_res_1482_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1489_, lean_object* v_idx_1490_, lean_object* v_e_1491_, lean_object* v_a_1492_, lean_object* v_00_u03b1_1493_, lean_object* v_x_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1500_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1501_ = l_Lean_mkProj(v_structName_1489_, v_idx_1490_, v_e_1491_);
v___x_1502_ = l_Lean_indentExpr(v___x_1501_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1500_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = l_Lean_indentExpr(v_a_1492_);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1507_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1509_, lean_object* v_idx_1510_, lean_object* v_e_1511_, lean_object* v_a_1512_, lean_object* v_00_u03b1_1513_, lean_object* v_x_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1509_, v_idx_1510_, v_e_1511_, v_a_1512_, v_00_u03b1_1513_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v_env_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1527_ = lean_st_ref_get(v___y_1525_);
v_env_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_ref(v_env_1528_);
lean_dec(v___x_1527_);
v___x_1529_ = 0;
lean_inc(v_constName_1521_);
v___x_1530_ = l_Lean_Environment_find_x3f(v_env_1528_, v_constName_1521_, v___x_1529_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
return v___x_1531_;
}
else
{
lean_object* v_val_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_constName_1521_);
v_val_1532_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1530_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_val_1532_);
lean_dec(v___x_1530_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 0);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_val_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1547_, lean_object* v_structName_1548_, lean_object* v_e_1549_, lean_object* v_idx_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_a_1560_; uint8_t v___x_1564_; 
v___x_1564_ = lean_nat_dec_lt(v_a_1552_, v_upperBound_1547_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; 
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_idx_1550_);
lean_dec_ref(v_e_1549_);
lean_dec(v_structName_1548_);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_b_1553_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; 
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
v___x_1566_ = lean_whnf(v_b_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
if (lean_obj_tag(v_a_1567_) == 7)
{
lean_object* v_body_1568_; uint8_t v___x_1569_; 
v_body_1568_ = lean_ctor_get(v_a_1567_, 2);
lean_inc_ref(v_body_1568_);
lean_dec_ref_known(v_a_1567_, 3);
v___x_1569_ = l_Lean_Expr_hasLooseBVars(v_body_1568_);
if (v___x_1569_ == 0)
{
v_a_1560_ = v_body_1568_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_inc_ref(v_e_1549_);
lean_inc(v_a_1552_);
lean_inc(v_structName_1548_);
v___x_1570_ = l_Lean_mkProj(v_structName_1548_, v_a_1552_, v_e_1549_);
v___x_1571_ = lean_expr_instantiate1(v_body_1568_, v___x_1570_);
lean_dec_ref(v___x_1570_);
lean_dec_ref(v_body_1568_);
v_a_1560_ = v___x_1571_;
goto v___jp_1559_;
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1572_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1549_);
lean_inc(v_idx_1550_);
lean_inc(v_structName_1548_);
v___x_1573_ = l_Lean_mkProj(v_structName_1548_, v_idx_1550_, v_e_1549_);
v___x_1574_ = l_Lean_indentExpr(v___x_1573_);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1572_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
lean_inc_ref(v_a_1551_);
v___x_1578_ = l_Lean_indentExpr(v_a_1551_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1579_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_dec_ref_known(v___x_1580_, 1);
v_a_1560_ = v_a_1567_;
goto v___jp_1559_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1567_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_idx_1550_);
lean_dec_ref(v_e_1549_);
lean_dec(v_structName_1548_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
else
{
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_idx_1550_);
lean_dec_ref(v_e_1549_);
lean_dec(v_structName_1548_);
return v___x_1566_;
}
}
v___jp_1559_:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = lean_nat_add(v_a_1552_, v___x_1561_);
lean_dec(v_a_1552_);
v_a_1552_ = v___x_1562_;
v_b_1553_ = v_a_1560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1589_, lean_object* v_structName_1590_, lean_object* v_e_1591_, lean_object* v_idx_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1589_, v_structName_1590_, v_e_1591_, v_idx_1592_, v_a_1593_, v_a_1594_, v_b_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v_upperBound_1589_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1602_, lean_object* v_structName_1603_, lean_object* v_e_1604_, lean_object* v_idx_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_b_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_a_1615_; uint8_t v___x_1619_; 
v___x_1619_ = lean_nat_dec_lt(v_a_1607_, v_upperBound_1602_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_idx_1605_);
lean_dec_ref(v_e_1604_);
lean_dec(v_structName_1603_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_b_1608_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; 
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1610_);
lean_inc_ref(v___y_1609_);
v___x_1621_ = lean_whnf(v_b_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
if (lean_obj_tag(v_a_1622_) == 7)
{
lean_object* v_body_1623_; uint8_t v___x_1624_; 
v_body_1623_ = lean_ctor_get(v_a_1622_, 2);
lean_inc_ref(v_body_1623_);
lean_dec_ref_known(v_a_1622_, 3);
v___x_1624_ = l_Lean_Expr_hasLooseBVars(v_body_1623_);
if (v___x_1624_ == 0)
{
v_a_1615_ = v_body_1623_;
goto v___jp_1614_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_inc_ref(v_e_1604_);
lean_inc(v_a_1607_);
lean_inc(v_structName_1603_);
v___x_1625_ = l_Lean_mkProj(v_structName_1603_, v_a_1607_, v_e_1604_);
v___x_1626_ = lean_expr_instantiate1(v_body_1623_, v___x_1625_);
lean_dec_ref(v___x_1625_);
lean_dec_ref(v_body_1623_);
v_a_1615_ = v___x_1626_;
goto v___jp_1614_;
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1604_);
lean_inc(v_idx_1605_);
lean_inc(v_structName_1603_);
v___x_1628_ = l_Lean_mkProj(v_structName_1603_, v_idx_1605_, v_e_1604_);
v___x_1629_ = l_Lean_indentExpr(v___x_1628_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1627_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
lean_inc_ref(v_a_1606_);
v___x_1633_ = l_Lean_indentExpr(v_a_1606_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1634_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_dec_ref_known(v___x_1635_, 1);
v_a_1615_ = v_a_1622_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1622_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_idx_1605_);
lean_dec_ref(v_e_1604_);
lean_dec(v_structName_1603_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
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
}
else
{
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_idx_1605_);
lean_dec_ref(v_e_1604_);
lean_dec(v_structName_1603_);
return v___x_1621_;
}
}
v___jp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = lean_unsigned_to_nat(1u);
v___x_1617_ = lean_nat_add(v_a_1607_, v___x_1616_);
lean_dec(v_a_1607_);
v___x_1618_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1602_, v_structName_1603_, v_e_1604_, v_idx_1605_, v_a_1606_, v___x_1617_, v_a_1615_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1644_, lean_object* v_structName_1645_, lean_object* v_e_1646_, lean_object* v_idx_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_b_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1644_, v_structName_1645_, v_e_1646_, v_idx_1647_, v_a_1648_, v_a_1649_, v_b_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v_upperBound_1644_);
return v_res_1656_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1657_; lean_object* v_dummy_1658_; 
v___x_1657_ = lean_box(0);
v_dummy_1658_ = l_Lean_Expr_sort___override(v___x_1657_);
return v_dummy_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1659_, lean_object* v_idx_1660_, lean_object* v_e_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v___x_1667_; 
lean_inc(v_a_1665_);
lean_inc_ref(v_a_1664_);
lean_inc(v_a_1663_);
lean_inc_ref(v_a_1662_);
lean_inc_ref(v_e_1661_);
v___x_1667_ = lean_infer_type(v_e_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
lean_inc(v_a_1665_);
lean_inc_ref(v_a_1664_);
lean_inc(v_a_1663_);
lean_inc_ref(v_a_1662_);
v___x_1669_ = lean_whnf(v_a_1668_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = l_Lean_Expr_getAppFn(v_a_1670_);
if (lean_obj_tag(v___x_1671_) == 4)
{
lean_object* v_declName_1672_; lean_object* v_us_1673_; lean_object* v___x_1674_; lean_object* v_env_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; 
v_declName_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_declName_1672_);
v_us_1673_ = lean_ctor_get(v___x_1671_, 1);
lean_inc(v_us_1673_);
lean_dec_ref_known(v___x_1671_, 2);
v___x_1674_ = lean_st_ref_get(v_a_1665_);
v_env_1678_ = lean_ctor_get(v___x_1674_, 0);
lean_inc_ref(v_env_1678_);
lean_dec(v___x_1674_);
v___x_1679_ = 0;
v___x_1680_ = l_Lean_Environment_find_x3f(v_env_1678_, v_declName_1672_, v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v_us_1673_);
v___x_1681_ = lean_box(0);
v___x_1682_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1681_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
return v___x_1682_;
}
else
{
lean_object* v_val_1683_; 
v_val_1683_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v___x_1680_, 1);
if (lean_obj_tag(v_val_1683_) == 5)
{
lean_object* v_val_1684_; lean_object* v_ctors_1685_; 
v_val_1684_ = lean_ctor_get(v_val_1683_, 0);
lean_inc_ref(v_val_1684_);
lean_dec_ref_known(v_val_1683_, 1);
v_ctors_1685_ = lean_ctor_get(v_val_1684_, 4);
lean_inc(v_ctors_1685_);
if (lean_obj_tag(v_ctors_1685_) == 1)
{
lean_object* v_tail_1686_; 
v_tail_1686_ = lean_ctor_get(v_ctors_1685_, 1);
if (lean_obj_tag(v_tail_1686_) == 0)
{
lean_object* v_toConstantVal_1687_; lean_object* v_numParams_1688_; lean_object* v_numIndices_1689_; lean_object* v_head_1690_; lean_object* v___x_1691_; 
v_toConstantVal_1687_ = lean_ctor_get(v_val_1684_, 0);
lean_inc_ref(v_toConstantVal_1687_);
v_numParams_1688_ = lean_ctor_get(v_val_1684_, 1);
lean_inc(v_numParams_1688_);
v_numIndices_1689_ = lean_ctor_get(v_val_1684_, 2);
lean_inc(v_numIndices_1689_);
lean_dec_ref(v_val_1684_);
v_head_1690_ = lean_ctor_get(v_ctors_1685_, 0);
lean_inc(v_head_1690_);
lean_dec_ref_known(v_ctors_1685_, 2);
v___x_1691_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1690_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
if (lean_obj_tag(v_a_1692_) == 6)
{
lean_object* v_val_1693_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v_name_1733_; uint8_t v___x_1734_; 
v_val_1693_ = lean_ctor_get(v_a_1692_, 0);
lean_inc_ref(v_val_1693_);
lean_dec_ref_known(v_a_1692_, 1);
v_name_1733_ = lean_ctor_get(v_toConstantVal_1687_, 0);
lean_inc(v_name_1733_);
lean_dec_ref(v_toConstantVal_1687_);
v___x_1734_ = lean_name_eq(v_name_1733_, v_structName_1659_);
lean_dec(v_name_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec_ref(v_val_1693_);
lean_dec(v_numIndices_1689_);
lean_dec(v_numParams_1688_);
lean_dec(v_us_1673_);
v___x_1735_ = lean_box(0);
v___x_1736_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1735_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
else
{
v___y_1695_ = v_a_1662_;
v___y_1696_ = v_a_1663_;
v___y_1697_ = v_a_1664_;
v___y_1698_ = v_a_1665_;
goto v___jp_1694_;
}
v___jp_1694_:
{
lean_object* v_dummy_1699_; lean_object* v_nargs_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_dummy_1699_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1700_ = l_Lean_Expr_getAppNumArgs(v_a_1670_);
lean_inc(v_nargs_1700_);
v___x_1701_ = lean_mk_array(v_nargs_1700_, v_dummy_1699_);
v___x_1702_ = lean_unsigned_to_nat(1u);
v___x_1703_ = lean_nat_sub(v_nargs_1700_, v___x_1702_);
lean_dec(v_nargs_1700_);
lean_inc(v_a_1670_);
v___x_1704_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1670_, v___x_1701_, v___x_1703_);
v___x_1705_ = lean_nat_add(v_numParams_1688_, v_numIndices_1689_);
lean_dec(v_numIndices_1689_);
v___x_1706_ = lean_array_get_size(v___x_1704_);
v___x_1707_ = lean_nat_dec_eq(v___x_1705_, v___x_1706_);
lean_dec(v___x_1705_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref(v___x_1704_);
lean_dec_ref(v_val_1693_);
lean_dec(v_numParams_1688_);
lean_dec(v_us_1673_);
v___x_1708_ = lean_box(0);
v___x_1709_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1708_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1709_;
}
else
{
lean_object* v_toConstantVal_1710_; lean_object* v_name_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_toConstantVal_1710_ = lean_ctor_get(v_val_1693_, 0);
lean_inc_ref(v_toConstantVal_1710_);
lean_dec_ref(v_val_1693_);
v_name_1711_ = lean_ctor_get(v_toConstantVal_1710_, 0);
lean_inc(v_name_1711_);
lean_dec_ref(v_toConstantVal_1710_);
v___x_1712_ = l_Lean_mkConst(v_name_1711_, v_us_1673_);
v___x_1713_ = lean_unsigned_to_nat(0u);
v___x_1714_ = l_Array_toSubarray___redArg(v___x_1704_, v___x_1713_, v_numParams_1688_);
v___x_1715_ = l_Subarray_copy___redArg(v___x_1714_);
v___x_1716_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1712_, v___x_1715_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec_ref(v___x_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
lean_inc(v_a_1670_);
lean_inc_ref(v_e_1661_);
lean_inc(v_structName_1659_);
lean_inc(v_idx_1660_);
v___x_1718_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1660_, v_structName_1659_, v_e_1661_, v_idx_1660_, v_a_1670_, v___x_1713_, v_a_1717_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
lean_inc(v___y_1698_);
lean_inc_ref(v___y_1697_);
lean_inc(v___y_1696_);
lean_inc_ref(v___y_1695_);
v___x_1720_ = lean_whnf(v_a_1719_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1732_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
if (lean_obj_tag(v_a_1721_) == 7)
{
lean_object* v_binderType_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
lean_dec(v_a_1670_);
lean_dec_ref(v_e_1661_);
lean_dec(v_idx_1660_);
lean_dec(v_structName_1659_);
v_binderType_1725_ = lean_ctor_get(v_a_1721_, 1);
lean_inc_ref(v_binderType_1725_);
lean_dec_ref_known(v_a_1721_, 3);
v___x_1726_ = lean_expr_consume_type_annotations(v_binderType_1725_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1726_);
v___x_1728_ = v___x_1723_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_del_object(v___x_1723_);
lean_dec(v_a_1721_);
v___x_1730_ = lean_box(0);
v___x_1731_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1730_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1731_;
}
}
}
else
{
lean_dec(v_a_1670_);
lean_dec_ref(v_e_1661_);
lean_dec(v_idx_1660_);
lean_dec(v_structName_1659_);
return v___x_1720_;
}
}
else
{
lean_dec(v_a_1670_);
lean_dec_ref(v_e_1661_);
lean_dec(v_idx_1660_);
lean_dec(v_structName_1659_);
return v___x_1718_;
}
}
else
{
lean_dec(v_a_1670_);
lean_dec_ref(v_e_1661_);
lean_dec(v_idx_1660_);
lean_dec(v_structName_1659_);
return v___x_1716_;
}
}
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec(v_a_1692_);
lean_dec(v_numIndices_1689_);
lean_dec(v_numParams_1688_);
lean_dec_ref(v_toConstantVal_1687_);
lean_dec(v_us_1673_);
v___x_1745_ = lean_box(0);
v___x_1746_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1745_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
return v___x_1746_;
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_numIndices_1689_);
lean_dec(v_numParams_1688_);
lean_dec_ref(v_toConstantVal_1687_);
lean_dec(v_us_1673_);
lean_dec(v_a_1670_);
lean_dec_ref(v_e_1661_);
lean_dec(v_idx_1660_);
lean_dec(v_structName_1659_);
v_a_1747_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1691_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1691_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1685_, 2);
lean_dec_ref(v_val_1684_);
lean_dec(v_us_1673_);
goto v___jp_1675_;
}
}
else
{
lean_dec(v_ctors_1685_);
lean_dec_ref(v_val_1684_);
lean_dec(v_us_1673_);
goto v___jp_1675_;
}
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_val_1683_);
lean_dec(v_us_1673_);
v___x_1755_ = lean_box(0);
v___x_1756_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1755_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
return v___x_1756_;
}
}
v___jp_1675_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1676_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
return v___x_1677_;
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec_ref(v___x_1671_);
v___x_1757_ = lean_box(0);
v___x_1758_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1659_, v_idx_1660_, v_e_1661_, v_a_1670_, lean_box(0), v___x_1757_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
return v___x_1758_;
}
}
else
{
lean_dec_ref(v_e_1661_);
lean_dec(v_idx_1660_);
lean_dec(v_structName_1659_);
return v___x_1669_;
}
}
else
{
lean_dec_ref(v_e_1661_);
lean_dec(v_idx_1660_);
lean_dec(v_structName_1659_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1759_, lean_object* v_idx_1760_, lean_object* v_e_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1759_, v_idx_1760_, v_e_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1768_, lean_object* v_structName_1769_, lean_object* v_e_1770_, lean_object* v_idx_1771_, lean_object* v_a_1772_, lean_object* v_inst_1773_, lean_object* v_R_1774_, lean_object* v_a_1775_, lean_object* v_b_1776_, lean_object* v_c_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1768_, v_structName_1769_, v_e_1770_, v_idx_1771_, v_a_1772_, v_a_1775_, v_b_1776_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1784_, lean_object* v_structName_1785_, lean_object* v_e_1786_, lean_object* v_idx_1787_, lean_object* v_a_1788_, lean_object* v_inst_1789_, lean_object* v_R_1790_, lean_object* v_a_1791_, lean_object* v_b_1792_, lean_object* v_c_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1784_, v_structName_1785_, v_e_1786_, v_idx_1787_, v_a_1788_, v_inst_1789_, v_R_1790_, v_a_1791_, v_b_1792_, v_c_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v_upperBound_1784_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1800_, lean_object* v_structName_1801_, lean_object* v_e_1802_, lean_object* v_idx_1803_, lean_object* v_a_1804_, lean_object* v_inst_1805_, lean_object* v_R_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_, lean_object* v_c_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1800_, v_structName_1801_, v_e_1802_, v_idx_1803_, v_a_1804_, v_a_1807_, v_b_1808_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1816_, lean_object* v_structName_1817_, lean_object* v_e_1818_, lean_object* v_idx_1819_, lean_object* v_a_1820_, lean_object* v_inst_1821_, lean_object* v_R_1822_, lean_object* v_a_1823_, lean_object* v_b_1824_, lean_object* v_c_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1816_, v_structName_1817_, v_e_1818_, v_idx_1819_, v_a_1820_, v_inst_1821_, v_R_1822_, v_a_1823_, v_b_1824_, v_c_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_upperBound_1816_);
return v_res_1831_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1841_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1842_ = l_Lean_indentExpr(v_type_1835_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1843_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1852_, lean_object* v_type_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_type_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1860_, v_type_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
lean_object* v_ks_1872_; lean_object* v_vs_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1897_; 
v_ks_1872_ = lean_ctor_get(v_x_1868_, 0);
v_vs_1873_ = lean_ctor_get(v_x_1868_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_x_1868_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1875_ = v_x_1868_;
v_isShared_1876_ = v_isSharedCheck_1897_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_vs_1873_);
lean_inc(v_ks_1872_);
lean_dec(v_x_1868_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1897_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = lean_array_get_size(v_ks_1872_);
v___x_1878_ = lean_nat_dec_lt(v_x_1869_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec(v_x_1869_);
v___x_1879_ = lean_array_push(v_ks_1872_, v_x_1870_);
v___x_1880_ = lean_array_push(v_vs_1873_, v_x_1871_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v___x_1880_);
lean_ctor_set(v___x_1875_, 0, v___x_1879_);
v___x_1882_ = v___x_1875_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
else
{
lean_object* v_k_x27_1884_; uint8_t v___x_1885_; 
v_k_x27_1884_ = lean_array_fget_borrowed(v_ks_1872_, v_x_1869_);
v___x_1885_ = l_Lean_instBEqMVarId_beq(v_x_1870_, v_k_x27_1884_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1887_; 
if (v_isShared_1876_ == 0)
{
v___x_1887_ = v___x_1875_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_ks_1872_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_vs_1873_);
v___x_1887_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_unsigned_to_nat(1u);
v___x_1889_ = lean_nat_add(v_x_1869_, v___x_1888_);
lean_dec(v_x_1869_);
v_x_1868_ = v___x_1887_;
v_x_1869_ = v___x_1889_;
goto _start;
}
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1892_ = lean_array_fset(v_ks_1872_, v_x_1869_, v_x_1870_);
v___x_1893_ = lean_array_fset(v_vs_1873_, v_x_1869_, v_x_1871_);
lean_dec(v_x_1869_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v___x_1893_);
lean_ctor_set(v___x_1875_, 0, v___x_1892_);
v___x_1895_ = v___x_1875_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1898_, lean_object* v_k_1899_, lean_object* v_v_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1898_, v___x_1901_, v_k_1899_, v_v_1900_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1904_, size_t v_x_1905_, size_t v_x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1904_) == 0)
{
lean_object* v_es_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v_j_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_es_1909_ = lean_ctor_get(v_x_1904_, 0);
v___x_1910_ = ((size_t)31ULL);
v___x_1911_ = lean_usize_land(v_x_1905_, v___x_1910_);
v_j_1912_ = lean_usize_to_nat(v___x_1911_);
v___x_1913_ = lean_array_get_size(v_es_1909_);
v___x_1914_ = lean_nat_dec_lt(v_j_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_dec(v_j_1912_);
lean_dec(v_x_1908_);
lean_dec(v_x_1907_);
return v_x_1904_;
}
else
{
lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1953_; 
lean_inc_ref(v_es_1909_);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_x_1904_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v_x_1904_, 0);
lean_dec(v_unused_1954_);
v___x_1916_ = v_x_1904_;
v_isShared_1917_ = v_isSharedCheck_1953_;
goto v_resetjp_1915_;
}
else
{
lean_dec(v_x_1904_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1953_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_v_1918_; lean_object* v___x_1919_; lean_object* v_xs_x27_1920_; lean_object* v___y_1922_; 
v_v_1918_ = lean_array_fget(v_es_1909_, v_j_1912_);
v___x_1919_ = lean_box(0);
v_xs_x27_1920_ = lean_array_fset(v_es_1909_, v_j_1912_, v___x_1919_);
switch(lean_obj_tag(v_v_1918_))
{
case 0:
{
lean_object* v_key_1927_; lean_object* v_val_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1938_; 
v_key_1927_ = lean_ctor_get(v_v_1918_, 0);
v_val_1928_ = lean_ctor_get(v_v_1918_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_v_1918_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1930_ = v_v_1918_;
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_val_1928_);
lean_inc(v_key_1927_);
lean_dec(v_v_1918_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint8_t v___x_1932_; 
v___x_1932_ = l_Lean_instBEqMVarId_beq(v_x_1907_, v_key_1927_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_del_object(v___x_1930_);
v___x_1933_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1927_, v_val_1928_, v_x_1907_, v_x_1908_);
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___y_1922_ = v___x_1934_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1936_; 
lean_dec(v_val_1928_);
lean_dec(v_key_1927_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_x_1908_);
lean_ctor_set(v___x_1930_, 0, v_x_1907_);
v___x_1936_ = v___x_1930_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_x_1907_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_x_1908_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
v___y_1922_ = v___x_1936_;
goto v___jp_1921_;
}
}
}
}
case 1:
{
lean_object* v_node_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1951_; 
v_node_1939_ = lean_ctor_get(v_v_1918_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_v_1918_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1941_ = v_v_1918_;
v_isShared_1942_ = v_isSharedCheck_1951_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_node_1939_);
lean_dec(v_v_1918_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1951_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
size_t v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1943_ = ((size_t)5ULL);
v___x_1944_ = lean_usize_shift_right(v_x_1905_, v___x_1943_);
v___x_1945_ = ((size_t)1ULL);
v___x_1946_ = lean_usize_add(v_x_1906_, v___x_1945_);
v___x_1947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1939_, v___x_1944_, v___x_1946_, v_x_1907_, v_x_1908_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1947_);
v___x_1949_ = v___x_1941_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
v___y_1922_ = v___x_1949_;
goto v___jp_1921_;
}
}
}
default: 
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_x_1907_);
lean_ctor_set(v___x_1952_, 1, v_x_1908_);
v___y_1922_ = v___x_1952_;
goto v___jp_1921_;
}
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_array_fset(v_xs_x27_1920_, v_j_1912_, v___y_1922_);
lean_dec(v_j_1912_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1923_);
v___x_1925_ = v___x_1916_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
else
{
lean_object* v_ks_1955_; lean_object* v_vs_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1976_; 
v_ks_1955_ = lean_ctor_get(v_x_1904_, 0);
v_vs_1956_ = lean_ctor_get(v_x_1904_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1904_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1958_ = v_x_1904_;
v_isShared_1959_ = v_isSharedCheck_1976_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_vs_1956_);
lean_inc(v_ks_1955_);
lean_dec(v_x_1904_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1976_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_ks_1955_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_vs_1956_);
v___x_1961_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v_newNode_1962_; uint8_t v___y_1964_; size_t v___x_1970_; uint8_t v___x_1971_; 
v_newNode_1962_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1961_, v_x_1907_, v_x_1908_);
v___x_1970_ = ((size_t)7ULL);
v___x_1971_ = lean_usize_dec_le(v___x_1970_, v_x_1906_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1962_);
v___x_1973_ = lean_unsigned_to_nat(4u);
v___x_1974_ = lean_nat_dec_lt(v___x_1972_, v___x_1973_);
lean_dec(v___x_1972_);
v___y_1964_ = v___x_1974_;
goto v___jp_1963_;
}
else
{
v___y_1964_ = v___x_1971_;
goto v___jp_1963_;
}
v___jp_1963_:
{
if (v___y_1964_ == 0)
{
lean_object* v_ks_1965_; lean_object* v_vs_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_ks_1965_ = lean_ctor_get(v_newNode_1962_, 0);
lean_inc_ref(v_ks_1965_);
v_vs_1966_ = lean_ctor_get(v_newNode_1962_, 1);
lean_inc_ref(v_vs_1966_);
lean_dec_ref(v_newNode_1962_);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1906_, v_ks_1965_, v_vs_1966_, v___x_1967_, v___x_1968_);
lean_dec_ref(v_vs_1966_);
lean_dec_ref(v_ks_1965_);
return v___x_1969_;
}
else
{
return v_newNode_1962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1977_, lean_object* v_keys_1978_, lean_object* v_vals_1979_, lean_object* v_i_1980_, lean_object* v_entries_1981_){
_start:
{
lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1982_ = lean_array_get_size(v_keys_1978_);
v___x_1983_ = lean_nat_dec_lt(v_i_1980_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_dec(v_i_1980_);
return v_entries_1981_;
}
else
{
lean_object* v_k_1984_; lean_object* v_v_1985_; uint64_t v___x_1986_; size_t v_h_1987_; size_t v___x_1988_; lean_object* v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; size_t v_h_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_k_1984_ = lean_array_fget_borrowed(v_keys_1978_, v_i_1980_);
v_v_1985_ = lean_array_fget_borrowed(v_vals_1979_, v_i_1980_);
v___x_1986_ = l_Lean_instHashableMVarId_hash(v_k_1984_);
v_h_1987_ = lean_uint64_to_usize(v___x_1986_);
v___x_1988_ = ((size_t)5ULL);
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_sub(v_depth_1977_, v___x_1990_);
v___x_1992_ = lean_usize_mul(v___x_1988_, v___x_1991_);
v_h_1993_ = lean_usize_shift_right(v_h_1987_, v___x_1992_);
v___x_1994_ = lean_nat_add(v_i_1980_, v___x_1989_);
lean_dec(v_i_1980_);
lean_inc(v_v_1985_);
lean_inc(v_k_1984_);
v___x_1995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1981_, v_h_1993_, v_depth_1977_, v_k_1984_, v_v_1985_);
v_i_1980_ = v___x_1994_;
v_entries_1981_ = v___x_1995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1997_, lean_object* v_keys_1998_, lean_object* v_vals_1999_, lean_object* v_i_2000_, lean_object* v_entries_2001_){
_start:
{
size_t v_depth_boxed_2002_; lean_object* v_res_2003_; 
v_depth_boxed_2002_ = lean_unbox_usize(v_depth_1997_);
lean_dec(v_depth_1997_);
v_res_2003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_2002_, v_keys_1998_, v_vals_1999_, v_i_2000_, v_entries_2001_);
lean_dec_ref(v_vals_1999_);
lean_dec_ref(v_keys_1998_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2004_, lean_object* v_x_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
size_t v_x_1234__boxed_2009_; size_t v_x_1235__boxed_2010_; lean_object* v_res_2011_; 
v_x_1234__boxed_2009_ = lean_unbox_usize(v_x_2005_);
lean_dec(v_x_2005_);
v_x_1235__boxed_2010_ = lean_unbox_usize(v_x_2006_);
lean_dec(v_x_2006_);
v_res_2011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2004_, v_x_1234__boxed_2009_, v_x_1235__boxed_2010_, v_x_2007_, v_x_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_){
_start:
{
uint64_t v___x_2015_; size_t v___x_2016_; size_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2015_ = l_Lean_instHashableMVarId_hash(v_x_2013_);
v___x_2016_ = lean_uint64_to_usize(v___x_2015_);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2012_, v___x_2016_, v___x_2017_, v_x_2013_, v_x_2014_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_2019_, lean_object* v_val_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v_mctx_2024_; lean_object* v_cache_2025_; lean_object* v_zetaDeltaFVarIds_2026_; lean_object* v_postponed_2027_; lean_object* v_diag_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2057_; 
v___x_2023_ = lean_st_ref_take(v___y_2021_);
v_mctx_2024_ = lean_ctor_get(v___x_2023_, 0);
v_cache_2025_ = lean_ctor_get(v___x_2023_, 1);
v_zetaDeltaFVarIds_2026_ = lean_ctor_get(v___x_2023_, 2);
v_postponed_2027_ = lean_ctor_get(v___x_2023_, 3);
v_diag_2028_ = lean_ctor_get(v___x_2023_, 4);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2030_ = v___x_2023_;
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_diag_2028_);
lean_inc(v_postponed_2027_);
lean_inc(v_zetaDeltaFVarIds_2026_);
lean_inc(v_cache_2025_);
lean_inc(v_mctx_2024_);
lean_dec(v___x_2023_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_depth_2032_; lean_object* v_levelAssignDepth_2033_; lean_object* v_lmvarCounter_2034_; lean_object* v_mvarCounter_2035_; lean_object* v_lDecls_2036_; lean_object* v_decls_2037_; lean_object* v_userNames_2038_; lean_object* v_lAssignment_2039_; lean_object* v_eAssignment_2040_; lean_object* v_dAssignment_2041_; lean_object* v_instanceTypedMVars_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2056_; 
v_depth_2032_ = lean_ctor_get(v_mctx_2024_, 0);
v_levelAssignDepth_2033_ = lean_ctor_get(v_mctx_2024_, 1);
v_lmvarCounter_2034_ = lean_ctor_get(v_mctx_2024_, 2);
v_mvarCounter_2035_ = lean_ctor_get(v_mctx_2024_, 3);
v_lDecls_2036_ = lean_ctor_get(v_mctx_2024_, 4);
v_decls_2037_ = lean_ctor_get(v_mctx_2024_, 5);
v_userNames_2038_ = lean_ctor_get(v_mctx_2024_, 6);
v_lAssignment_2039_ = lean_ctor_get(v_mctx_2024_, 7);
v_eAssignment_2040_ = lean_ctor_get(v_mctx_2024_, 8);
v_dAssignment_2041_ = lean_ctor_get(v_mctx_2024_, 9);
v_instanceTypedMVars_2042_ = lean_ctor_get(v_mctx_2024_, 10);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_mctx_2024_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2044_ = v_mctx_2024_;
v_isShared_2045_ = v_isSharedCheck_2056_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_instanceTypedMVars_2042_);
lean_inc(v_dAssignment_2041_);
lean_inc(v_eAssignment_2040_);
lean_inc(v_lAssignment_2039_);
lean_inc(v_userNames_2038_);
lean_inc(v_decls_2037_);
lean_inc(v_lDecls_2036_);
lean_inc(v_mvarCounter_2035_);
lean_inc(v_lmvarCounter_2034_);
lean_inc(v_levelAssignDepth_2033_);
lean_inc(v_depth_2032_);
lean_dec(v_mctx_2024_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2056_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_2040_, v_mvarId_2019_, v_val_2020_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 8, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_depth_2032_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_levelAssignDepth_2033_);
lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_lmvarCounter_2034_);
lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_mvarCounter_2035_);
lean_ctor_set(v_reuseFailAlloc_2055_, 4, v_lDecls_2036_);
lean_ctor_set(v_reuseFailAlloc_2055_, 5, v_decls_2037_);
lean_ctor_set(v_reuseFailAlloc_2055_, 6, v_userNames_2038_);
lean_ctor_set(v_reuseFailAlloc_2055_, 7, v_lAssignment_2039_);
lean_ctor_set(v_reuseFailAlloc_2055_, 8, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2055_, 9, v_dAssignment_2041_);
lean_ctor_set(v_reuseFailAlloc_2055_, 10, v_instanceTypedMVars_2042_);
v___x_2048_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2048_);
v___x_2050_ = v___x_2030_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_cache_2025_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_zetaDeltaFVarIds_2026_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_postponed_2027_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_diag_2028_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = lean_st_ref_put(v___y_2021_, v___x_2050_);
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_2058_, lean_object* v_val_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2058_, v_val_2059_, v___y_2060_);
lean_dec(v___y_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2069_; 
lean_inc(v_a_2067_);
lean_inc_ref(v_a_2066_);
lean_inc(v_a_2065_);
lean_inc_ref(v_a_2064_);
lean_inc_ref(v_type_2063_);
v___x_2069_ = lean_infer_type(v_type_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = l_Lean_Meta_whnfD(v_a_2070_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2106_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2106_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2106_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
switch(lean_obj_tag(v_a_2072_))
{
case 3:
{
lean_object* v_u_2076_; lean_object* v___x_2078_; 
lean_dec_ref(v_type_2063_);
v_u_2076_ = lean_ctor_get(v_a_2072_, 0);
lean_inc(v_u_2076_);
lean_dec_ref_known(v_a_2072_, 1);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v_u_2076_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_u_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
case 2:
{
lean_object* v_mvarId_2080_; lean_object* v___x_2081_; 
lean_del_object(v___x_2074_);
v_mvarId_2080_ = lean_ctor_get(v_a_2072_, 0);
lean_inc_n(v_mvarId_2080_, 2);
lean_dec_ref_known(v_a_2072_, 1);
v___x_2081_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_2080_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; uint8_t v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = lean_unbox(v_a_2082_);
lean_dec(v_a_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_dec_ref(v_type_2063_);
v___x_2084_ = l_Lean_Meta_mkFreshLevelMVar(v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc_n(v_a_2085_, 2);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = l_Lean_mkSort(v_a_2085_);
v___x_2087_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2080_, v___x_2086_, v_a_2065_);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2095_);
v___x_2089_ = v___x_2087_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v___x_2087_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v_a_2085_);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2085_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_dec(v_mvarId_2080_);
return v___x_2084_;
}
}
else
{
lean_object* v___x_2096_; 
lean_dec(v_mvarId_2080_);
v___x_2096_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
return v___x_2096_;
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_mvarId_2080_);
lean_dec_ref(v_type_2063_);
v_a_2097_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2081_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2081_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
default: 
{
lean_object* v___x_2105_; 
lean_del_object(v___x_2074_);
lean_dec(v_a_2072_);
v___x_2105_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v_type_2063_);
v_a_2107_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2071_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2071_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_type_2063_);
v_a_2115_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2069_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2069_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_getLevel(v_type_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_2130_, lean_object* v_val_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_2130_, v_val_2131_, v___y_2133_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_2138_, lean_object* v_val_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_2138_, v_val_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_2147_, v_x_2148_, v_x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2151_, lean_object* v_x_2152_, size_t v_x_2153_, size_t v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_2152_, v_x_2153_, v_x_2154_, v_x_2155_, v_x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
size_t v_x_1587__boxed_2164_; size_t v_x_1588__boxed_2165_; lean_object* v_res_2166_; 
v_x_1587__boxed_2164_ = lean_unbox_usize(v_x_2160_);
lean_dec(v_x_2160_);
v_x_1588__boxed_2165_ = lean_unbox_usize(v_x_2161_);
lean_dec(v_x_2161_);
v_res_2166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_2158_, v_x_2159_, v_x_1587__boxed_2164_, v_x_1588__boxed_2165_, v_x_2162_, v_x_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2167_, lean_object* v_n_2168_, lean_object* v_k_2169_, lean_object* v_v_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2168_, v_k_2169_, v_v_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2172_, size_t v_depth_2173_, lean_object* v_keys_2174_, lean_object* v_vals_2175_, lean_object* v_heq_2176_, lean_object* v_i_2177_, lean_object* v_entries_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2173_, v_keys_2174_, v_vals_2175_, v_i_2177_, v_entries_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2180_, lean_object* v_depth_2181_, lean_object* v_keys_2182_, lean_object* v_vals_2183_, lean_object* v_heq_2184_, lean_object* v_i_2185_, lean_object* v_entries_2186_){
_start:
{
size_t v_depth_boxed_2187_; lean_object* v_res_2188_; 
v_depth_boxed_2187_ = lean_unbox_usize(v_depth_2181_);
lean_dec(v_depth_2181_);
v_res_2188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2180_, v_depth_boxed_2187_, v_keys_2182_, v_vals_2183_, v_heq_2184_, v_i_2185_, v_entries_2186_);
lean_dec_ref(v_vals_2183_);
lean_dec_ref(v_keys_2182_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2190_, v_x_2191_, v_x_2192_, v_x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_2195_, lean_object* v_b_2196_, lean_object* v_c_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
v___x_2203_ = lean_apply_7(v_k_2195_, v_b_2196_, v_c_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, lean_box(0));
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_2204_, lean_object* v_b_2205_, lean_object* v_c_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_2204_, v_b_2205_, v_c_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_2213_, lean_object* v_k_2214_, uint8_t v_cleanupAnnotations_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___f_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___f_2221_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2221_, 0, v_k_2214_);
v___x_2222_ = 0;
v___x_2223_ = lean_box(0);
v___x_2224_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2222_, v___x_2223_, v_type_2213_, v___f_2221_, v_cleanupAnnotations_2215_, v___x_2222_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_a_2233_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2224_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2224_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_2241_, lean_object* v_k_2242_, lean_object* v_cleanupAnnotations_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2249_; lean_object* v_res_2250_; 
v_cleanupAnnotations_boxed_2249_ = lean_unbox(v_cleanupAnnotations_2243_);
v_res_2250_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2241_, v_k_2242_, v_cleanupAnnotations_boxed_2249_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_2251_, lean_object* v_type_2252_, lean_object* v_k_2253_, uint8_t v_cleanupAnnotations_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2252_, v_k_2253_, v_cleanupAnnotations_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2261_, lean_object* v_type_2262_, lean_object* v_k_2263_, lean_object* v_cleanupAnnotations_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2270_; lean_object* v_res_2271_; 
v_cleanupAnnotations_boxed_2270_ = lean_unbox(v_cleanupAnnotations_2264_);
v_res_2271_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2261_, v_type_2262_, v_k_2263_, v_cleanupAnnotations_boxed_2270_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2272_, size_t v_i_2273_, size_t v_stop_2274_, lean_object* v_b_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_usize_dec_eq(v_i_2273_, v_stop_2274_);
if (v___x_2281_ == 0)
{
size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_sub(v_i_2273_, v___x_2282_);
v___x_2284_ = lean_array_uget_borrowed(v_as_2272_, v___x_2283_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___x_2284_);
v___x_2285_ = lean_infer_type(v___x_2284_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = l_Lean_Meta_getLevel(v_a_2286_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = l_Lean_mkLevelIMax_x27(v_a_2288_, v_b_2275_);
v_i_2273_ = v___x_2283_;
v_b_2275_ = v___x_2289_;
goto _start;
}
else
{
lean_dec(v_b_2275_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2291_; 
v_a_2291_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2287_, 1);
v_i_2273_ = v___x_2283_;
v_b_2275_ = v_a_2291_;
goto _start;
}
else
{
return v___x_2287_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_b_2275_);
v_a_2293_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2285_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2285_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_b_2275_);
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2302_, lean_object* v_i_2303_, lean_object* v_stop_2304_, lean_object* v_b_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
size_t v_i_boxed_2311_; size_t v_stop_boxed_2312_; lean_object* v_res_2313_; 
v_i_boxed_2311_ = lean_unbox_usize(v_i_2303_);
lean_dec(v_i_2303_);
v_stop_boxed_2312_ = lean_unbox_usize(v_stop_2304_);
lean_dec(v_stop_2304_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2302_, v_i_boxed_2311_, v_stop_boxed_2312_, v_b_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec_ref(v_as_2302_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2314_, lean_object* v_e_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___y_2322_; lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Meta_getLevel(v_e_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
v___x_2343_ = lean_array_get_size(v_xs_2314_);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = lean_nat_dec_lt(v___x_2344_, v___x_2343_);
if (v___x_2345_ == 0)
{
lean_dec(v_a_2342_);
v___y_2322_ = v___x_2341_;
goto v___jp_2321_;
}
else
{
size_t v___x_2346_; size_t v___x_2347_; lean_object* v___x_2348_; 
lean_dec_ref_known(v___x_2341_, 1);
v___x_2346_ = lean_usize_of_nat(v___x_2343_);
v___x_2347_ = ((size_t)0ULL);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2314_, v___x_2346_, v___x_2347_, v_a_2342_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
v___y_2322_ = v___x_2348_;
goto v___jp_2321_;
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_a_2349_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2341_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2341_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
v___jp_2321_:
{
if (lean_obj_tag(v___y_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2332_; 
v_a_2323_ = lean_ctor_get(v___y_2322_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___y_2322_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2325_ = v___y_2322_;
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___y_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = l_Lean_Level_normalize(v_a_2323_);
lean_dec(v_a_2323_);
v___x_2328_ = l_Lean_mkSort(v___x_2327_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_a_2333_ = lean_ctor_get(v___y_2322_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___y_2322_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___y_2322_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___y_2322_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2357_, lean_object* v_e_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2357_, v_e_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_xs_2357_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___f_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; 
v___f_2372_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2373_ = 0;
v___x_2374_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2366_, v___f_2372_, v___x_2373_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2382_, lean_object* v_k_2383_, uint8_t v_cleanupAnnotations_2384_, uint8_t v_preserveNondepLet_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___f_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___f_2391_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2391_, 0, v_k_2383_);
v___x_2392_ = 1;
v___x_2393_ = 0;
v___x_2394_ = lean_box(0);
v___x_2395_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2382_, v___x_2392_, v___x_2392_, v_preserveNondepLet_2385_, v___x_2393_, v___x_2394_, v___f_2391_, v_cleanupAnnotations_2384_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_a_2404_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2395_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2395_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2412_, lean_object* v_k_2413_, lean_object* v_cleanupAnnotations_2414_, lean_object* v_preserveNondepLet_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2421_; uint8_t v_preserveNondepLet_boxed_2422_; lean_object* v_res_2423_; 
v_cleanupAnnotations_boxed_2421_ = lean_unbox(v_cleanupAnnotations_2414_);
v_preserveNondepLet_boxed_2422_ = lean_unbox(v_preserveNondepLet_2415_);
v_res_2423_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2412_, v_k_2413_, v_cleanupAnnotations_boxed_2421_, v_preserveNondepLet_boxed_2422_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2424_, lean_object* v_e_2425_, lean_object* v_k_2426_, uint8_t v_cleanupAnnotations_2427_, uint8_t v_preserveNondepLet_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2425_, v_k_2426_, v_cleanupAnnotations_2427_, v_preserveNondepLet_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_e_2436_, lean_object* v_k_2437_, lean_object* v_cleanupAnnotations_2438_, lean_object* v_preserveNondepLet_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2445_; uint8_t v_preserveNondepLet_boxed_2446_; lean_object* v_res_2447_; 
v_cleanupAnnotations_boxed_2445_ = lean_unbox(v_cleanupAnnotations_2438_);
v_preserveNondepLet_boxed_2446_ = lean_unbox(v_preserveNondepLet_2439_);
v_res_2447_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2435_, v_e_2436_, v_k_2437_, v_cleanupAnnotations_boxed_2445_, v_preserveNondepLet_boxed_2446_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2448_, lean_object* v_e_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
v___x_2455_ = lean_infer_type(v_e_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; uint8_t v___x_2457_; uint8_t v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = 0;
v___x_2458_ = 1;
v___x_2459_ = 1;
v___x_2460_ = l_Lean_Meta_mkForallFVars(v_xs_2448_, v_a_2456_, v___x_2457_, v___x_2458_, v___x_2457_, v___x_2459_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2460_;
}
else
{
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2461_, lean_object* v_e_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2461_, v_e_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec_ref(v_xs_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v___f_2476_; uint8_t v___x_2477_; uint8_t v___x_2478_; lean_object* v___x_2479_; 
v___f_2476_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2477_ = 0;
v___x_2478_ = 1;
v___x_2479_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2470_, v___f_2476_, v___x_2477_, v___x_2478_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
return v_res_2486_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2499_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2500_ = l_Lean_MessageData_ofName(v_mvarId_2493_);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2503_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2512_, lean_object* v_mvarId_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2520_, lean_object* v_mvarId_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2520_, v_mvarId_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v_mctx_2535_; lean_object* v___x_2536_; 
v___x_2534_ = lean_st_ref_get(v_a_2530_);
v_mctx_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_mctx_2535_);
lean_dec(v___x_2534_);
v___x_2536_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2535_, v_mvarId_2528_);
lean_dec_ref(v_mctx_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
return v___x_2537_;
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_mvarId_2528_);
v_val_2538_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_val_2538_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2546_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_type_2542_; lean_object* v___x_2544_; 
v_type_2542_ = lean_ctor_get(v_val_2538_, 2);
lean_inc_ref(v_type_2542_);
lean_dec(v_val_2538_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 0);
lean_ctor_set(v___x_2540_, 0, v_type_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_type_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_lctx_2559_; lean_object* v___x_2560_; 
v_lctx_2559_ = lean_ctor_get(v_a_2555_, 2);
lean_inc(v_fvarId_2554_);
lean_inc_ref(v_lctx_2559_);
v___x_2560_ = lean_local_ctx_find(v_lctx_2559_, v_fvarId_2554_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2554_, v_a_2556_, v_a_2557_);
return v___x_2561_;
}
else
{
lean_object* v_val_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_fvarId_2554_);
v_val_2562_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2564_ = v___x_2560_;
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_val_2562_);
lean_dec(v___x_2560_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = l_Lean_LocalDecl_type(v_val_2562_);
lean_dec(v_val_2562_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2568_ = v___x_2564_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2571_, v_a_2572_, v_a_2573_, v_a_2574_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec_ref(v_a_2572_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2577_, v_a_2578_, v_a_2580_, v_a_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
return v_res_2590_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_instMonadEIO(lean_box(0));
return v___x_2591_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2593_ = l_StateRefT_x27_instMonad___redArg(v___x_2592_);
return v___x_2593_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2596_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___f_2598_; 
v___x_2597_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2598_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2598_, 0, v___x_2597_);
return v___f_2598_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___f_2600_; 
v___x_2599_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2600_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2600_, 0, v___x_2599_);
return v___f_2600_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; 
v___f_2601_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2602_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___f_2602_);
lean_ctor_set(v___x_2603_, 1, v___f_2601_);
return v___x_2603_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___f_2605_; 
v___x_2604_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2605_, 0, v___x_2604_);
return v___f_2605_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___f_2607_; 
v___x_2606_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2607_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2607_, 0, v___x_2606_);
return v___f_2607_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; 
v___f_2608_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2609_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___f_2609_);
lean_ctor_set(v___x_2610_, 1, v___f_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2613_, lean_object* v_inferType_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
uint8_t v_cacheInferType_2658_; 
v_cacheInferType_2658_ = lean_ctor_get_uint8(v_a_2615_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2658_ == 0)
{
lean_dec_ref(v_e_2613_);
goto v___jp_2620_;
}
else
{
uint8_t v___x_2659_; 
v___x_2659_ = l_Lean_Expr_hasMVar(v_e_2613_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2613_, v_a_2615_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2761_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2663_ = v___x_2660_;
v_isShared_2664_ = v_isSharedCheck_2761_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2761_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2707_; lean_object* v_cache_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2756_; 
v___x_2707_ = lean_st_ref_get(v_a_2616_);
v_cache_2708_ = lean_ctor_get(v___x_2707_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; lean_object* v_unused_2758_; lean_object* v_unused_2759_; lean_object* v_unused_2760_; 
v_unused_2757_ = lean_ctor_get(v___x_2707_, 4);
lean_dec(v_unused_2757_);
v_unused_2758_ = lean_ctor_get(v___x_2707_, 3);
lean_dec(v_unused_2758_);
v_unused_2759_ = lean_ctor_get(v___x_2707_, 2);
lean_dec(v_unused_2759_);
v_unused_2760_ = lean_ctor_get(v___x_2707_, 0);
lean_dec(v_unused_2760_);
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2756_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_cache_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2756_;
goto v_resetjp_2709_;
}
v___jp_2665_:
{
lean_object* v___x_2666_; 
lean_inc(v_a_2618_);
lean_inc_ref(v_a_2617_);
lean_inc(v_a_2616_);
lean_inc_ref(v_a_2615_);
v___x_2666_ = lean_apply_5(v_inferType_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, lean_box(0));
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; uint8_t v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
v___x_2668_ = l_Lean_Expr_hasMVar(v_a_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2705_; 
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; 
v_unused_2706_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2706_);
v___x_2670_ = v___x_2666_;
v_isShared_2671_ = v_isSharedCheck_2705_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v___x_2666_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2705_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v_cache_2673_; lean_object* v_mctx_2674_; lean_object* v_zetaDeltaFVarIds_2675_; lean_object* v_postponed_2676_; lean_object* v_diag_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2704_; 
v___x_2672_ = lean_st_ref_take(v_a_2616_);
v_cache_2673_ = lean_ctor_get(v___x_2672_, 1);
v_mctx_2674_ = lean_ctor_get(v___x_2672_, 0);
v_zetaDeltaFVarIds_2675_ = lean_ctor_get(v___x_2672_, 2);
v_postponed_2676_ = lean_ctor_get(v___x_2672_, 3);
v_diag_2677_ = lean_ctor_get(v___x_2672_, 4);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2679_ = v___x_2672_;
v_isShared_2680_ = v_isSharedCheck_2704_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_diag_2677_);
lean_inc(v_postponed_2676_);
lean_inc(v_zetaDeltaFVarIds_2675_);
lean_inc(v_cache_2673_);
lean_inc(v_mctx_2674_);
lean_dec(v___x_2672_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2704_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_inferType_2681_; lean_object* v_funInfo_2682_; lean_object* v_synthInstance_2683_; lean_object* v_whnf_2684_; lean_object* v_defEqTrans_2685_; lean_object* v_defEqPerm_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2703_; 
v_inferType_2681_ = lean_ctor_get(v_cache_2673_, 0);
v_funInfo_2682_ = lean_ctor_get(v_cache_2673_, 1);
v_synthInstance_2683_ = lean_ctor_get(v_cache_2673_, 2);
v_whnf_2684_ = lean_ctor_get(v_cache_2673_, 3);
v_defEqTrans_2685_ = lean_ctor_get(v_cache_2673_, 4);
v_defEqPerm_2686_ = lean_ctor_get(v_cache_2673_, 5);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_cache_2673_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2688_ = v_cache_2673_;
v_isShared_2689_ = v_isSharedCheck_2703_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_defEqPerm_2686_);
lean_inc(v_defEqTrans_2685_);
lean_inc(v_whnf_2684_);
lean_inc(v_synthInstance_2683_);
lean_inc(v_funInfo_2682_);
lean_inc(v_inferType_2681_);
lean_dec(v_cache_2673_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2703_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___f_2690_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2667_);
v___x_2692_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2690_, v___x_2691_, v_inferType_2681_, v_a_2661_, v_a_2667_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2692_);
v___x_2694_ = v___x_2688_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_funInfo_2682_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_synthInstance_2683_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_whnf_2684_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_defEqTrans_2685_);
lean_ctor_set(v_reuseFailAlloc_2702_, 5, v_defEqPerm_2686_);
v___x_2694_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 1, v___x_2694_);
v___x_2696_ = v___x_2679_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_mctx_2674_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_zetaDeltaFVarIds_2675_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_postponed_2676_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_diag_2677_);
v___x_2696_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_st_ref_put(v_a_2616_, v___x_2696_);
if (v_isShared_2671_ == 0)
{
v___x_2699_ = v___x_2670_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2667_);
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
}
else
{
lean_dec(v_a_2667_);
lean_dec(v_a_2661_);
return v___x_2666_;
}
}
else
{
lean_dec(v_a_2661_);
return v___x_2666_;
}
}
v_resetjp_2709_:
{
lean_object* v_inferType_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_inferType_2712_ = lean_ctor_get(v_cache_2708_, 0);
lean_inc_ref(v_inferType_2712_);
lean_dec_ref(v_cache_2708_);
v___f_2713_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2661_);
v___x_2715_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2713_, v___x_2714_, v_inferType_2712_, v_a_2661_);
lean_dec_ref(v_inferType_2712_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v___x_2716_; lean_object* v_toApplicative_2717_; lean_object* v_toFunctor_2718_; lean_object* v_toSeq_2719_; lean_object* v_toSeqLeft_2720_; lean_object* v_toSeqRight_2721_; lean_object* v___f_2722_; lean_object* v___f_2723_; lean_object* v___f_2724_; lean_object* v___f_2725_; lean_object* v___x_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v___f_2729_; lean_object* v___x_2731_; 
lean_del_object(v___x_2663_);
v___x_2716_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2717_ = lean_ctor_get(v___x_2716_, 0);
v_toFunctor_2718_ = lean_ctor_get(v_toApplicative_2717_, 0);
v_toSeq_2719_ = lean_ctor_get(v_toApplicative_2717_, 2);
v_toSeqLeft_2720_ = lean_ctor_get(v_toApplicative_2717_, 3);
v_toSeqRight_2721_ = lean_ctor_get(v_toApplicative_2717_, 4);
v___f_2722_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2723_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2718_, 2);
v___f_2724_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2724_, 0, v_toFunctor_2718_);
v___f_2725_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2725_, 0, v_toFunctor_2718_);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___f_2724_);
lean_ctor_set(v___x_2726_, 1, v___f_2725_);
lean_inc(v_toSeqRight_2721_);
v___f_2727_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2727_, 0, v_toSeqRight_2721_);
lean_inc(v_toSeqLeft_2720_);
v___f_2728_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2728_, 0, v_toSeqLeft_2720_);
lean_inc(v_toSeq_2719_);
v___f_2729_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2729_, 0, v_toSeq_2719_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 4, v___f_2727_);
lean_ctor_set(v___x_2710_, 3, v___f_2728_);
lean_ctor_set(v___x_2710_, 2, v___f_2729_);
lean_ctor_set(v___x_2710_, 1, v___f_2722_);
lean_ctor_set(v___x_2710_, 0, v___x_2726_);
v___x_2731_ = v___x_2710_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___f_2722_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v___f_2729_);
lean_ctor_set(v_reuseFailAlloc_2751_, 3, v___f_2728_);
lean_ctor_set(v_reuseFailAlloc_2751_, 4, v___f_2727_);
v___x_2731_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v_cancelTk_x3f_2733_; 
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v___f_2723_);
v_cancelTk_x3f_2733_ = lean_ctor_get(v_a_2617_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2733_) == 1)
{
lean_object* v_val_2734_; uint8_t v___x_2735_; 
v_val_2734_ = lean_ctor_get(v_cancelTk_x3f_2733_, 0);
v___x_2735_ = l_IO_CancelToken_isSet(v_val_2734_);
if (v___x_2735_ == 0)
{
lean_dec_ref_known(v___x_2732_, 2);
goto v___jp_2665_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2392__overap_2741_; lean_object* v___x_2742_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2737_ = l_Lean_Core_instMonadRefCoreM;
v___x_2738_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2739_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2738_, v___x_2732_);
v___x_2740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2736_);
lean_ctor_set(v___x_2740_, 1, v___x_2737_);
lean_ctor_set(v___x_2740_, 2, v___x_2739_);
v___x_2392__overap_2741_ = l_Lean_throwInterruptException___redArg(v___x_2740_);
lean_inc(v_a_2618_);
lean_inc_ref(v_a_2617_);
v___x_2742_ = lean_apply_3(v___x_2392__overap_2741_, v_a_2617_, v_a_2618_, lean_box(0));
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_dec_ref_known(v___x_2742_, 1);
goto v___jp_2665_;
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2661_);
lean_dec_ref(v_inferType_2614_);
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2732_, 2);
goto v___jp_2665_;
}
}
}
else
{
lean_object* v_val_2752_; lean_object* v___x_2754_; 
lean_del_object(v___x_2710_);
lean_dec(v_a_2661_);
lean_dec_ref(v_inferType_2614_);
v_val_2752_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_val_2752_);
lean_dec_ref_known(v___x_2715_, 1);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v_val_2752_);
v___x_2754_ = v___x_2663_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_val_2752_);
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
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v_inferType_2614_);
v_a_2762_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2660_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2660_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_dec_ref(v_e_2613_);
goto v___jp_2620_;
}
}
v___jp_2620_:
{
lean_object* v___x_2621_; lean_object* v_toApplicative_2622_; lean_object* v_toFunctor_2623_; lean_object* v_toSeq_2624_; lean_object* v_toSeqLeft_2625_; lean_object* v_toSeqRight_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; lean_object* v___f_2632_; lean_object* v___f_2633_; lean_object* v___f_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v_cancelTk_x3f_2637_; 
v___x_2621_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2622_ = lean_ctor_get(v___x_2621_, 0);
v_toFunctor_2623_ = lean_ctor_get(v_toApplicative_2622_, 0);
v_toSeq_2624_ = lean_ctor_get(v_toApplicative_2622_, 2);
v_toSeqLeft_2625_ = lean_ctor_get(v_toApplicative_2622_, 3);
v_toSeqRight_2626_ = lean_ctor_get(v_toApplicative_2622_, 4);
v___f_2627_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2628_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2623_, 2);
v___f_2629_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2629_, 0, v_toFunctor_2623_);
v___f_2630_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2630_, 0, v_toFunctor_2623_);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___f_2629_);
lean_ctor_set(v___x_2631_, 1, v___f_2630_);
lean_inc(v_toSeqRight_2626_);
v___f_2632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2632_, 0, v_toSeqRight_2626_);
lean_inc(v_toSeqLeft_2625_);
v___f_2633_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2633_, 0, v_toSeqLeft_2625_);
lean_inc(v_toSeq_2624_);
v___f_2634_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2634_, 0, v_toSeq_2624_);
v___x_2635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2631_);
lean_ctor_set(v___x_2635_, 1, v___f_2627_);
lean_ctor_set(v___x_2635_, 2, v___f_2634_);
lean_ctor_set(v___x_2635_, 3, v___f_2633_);
lean_ctor_set(v___x_2635_, 4, v___f_2632_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___f_2628_);
v_cancelTk_x3f_2637_ = lean_ctor_get(v_a_2617_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2637_) == 1)
{
lean_object* v_val_2638_; uint8_t v___x_2639_; 
v_val_2638_ = lean_ctor_get(v_cancelTk_x3f_2637_, 0);
v___x_2639_ = l_IO_CancelToken_isSet(v_val_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref_known(v___x_2636_, 2);
lean_inc(v_a_2618_);
lean_inc_ref(v_a_2617_);
lean_inc(v_a_2616_);
lean_inc_ref(v_a_2615_);
v___x_2640_ = lean_apply_5(v_inferType_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, lean_box(0));
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2189__overap_2646_; lean_object* v___x_2647_; 
v___x_2641_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2642_ = l_Lean_Core_instMonadRefCoreM;
v___x_2643_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2644_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2643_, v___x_2636_);
v___x_2645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2641_);
lean_ctor_set(v___x_2645_, 1, v___x_2642_);
lean_ctor_set(v___x_2645_, 2, v___x_2644_);
v___x_2189__overap_2646_ = l_Lean_throwInterruptException___redArg(v___x_2645_);
lean_inc(v_a_2618_);
lean_inc_ref(v_a_2617_);
v___x_2647_ = lean_apply_3(v___x_2189__overap_2646_, v_a_2617_, v_a_2618_, lean_box(0));
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2648_; 
lean_dec_ref_known(v___x_2647_, 1);
lean_inc(v_a_2618_);
lean_inc_ref(v_a_2617_);
lean_inc(v_a_2616_);
lean_inc_ref(v_a_2615_);
v___x_2648_ = lean_apply_5(v_inferType_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, lean_box(0));
return v___x_2648_;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v_inferType_2614_);
v_a_2649_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2647_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2647_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
else
{
lean_object* v___x_2657_; 
lean_dec_ref_known(v___x_2636_, 2);
lean_inc(v_a_2618_);
lean_inc_ref(v_a_2617_);
lean_inc(v_a_2616_);
lean_inc_ref(v_a_2615_);
v___x_2657_ = lean_apply_5(v_inferType_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, lean_box(0));
return v___x_2657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2770_, lean_object* v_inferType_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2770_, v_inferType_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___y_2785_; uint8_t v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; uint8_t v___y_2789_; uint8_t v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; uint8_t v___y_2825_; lean_object* v___x_2852_; uint8_t v_transparency_2853_; uint8_t v___x_2854_; uint8_t v___x_2855_; 
v___x_2852_ = l_Lean_Meta_Context_config(v_a_2779_);
v_transparency_2853_ = lean_ctor_get_uint8(v___x_2852_, 9);
lean_dec_ref(v___x_2852_);
v___x_2854_ = 1;
v___x_2855_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2853_, v___x_2854_);
if (v___x_2855_ == 0)
{
v___y_2825_ = v_transparency_2853_;
goto v___jp_2824_;
}
else
{
v___y_2825_ = v___x_2854_;
goto v___jp_2824_;
}
v___jp_2784_:
{
lean_object* v___x_2796_; uint8_t v_foApprox_2797_; uint8_t v_ctxApprox_2798_; uint8_t v_quasiPatternApprox_2799_; uint8_t v_constApprox_2800_; uint8_t v_isDefEqStuckEx_2801_; uint8_t v_unificationHints_2802_; uint8_t v_proofIrrelevance_2803_; uint8_t v_assignSyntheticOpaque_2804_; uint8_t v_offsetCnstrs_2805_; uint8_t v_transparency_2806_; uint8_t v_univApprox_2807_; uint8_t v_zetaUnused_2808_; uint8_t v_canUnfoldPredicateConfig_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2823_; 
v___x_2796_ = l_Lean_Meta_Context_config(v___y_2793_);
lean_dec_ref(v___y_2793_);
v_foApprox_2797_ = lean_ctor_get_uint8(v___x_2796_, 0);
v_ctxApprox_2798_ = lean_ctor_get_uint8(v___x_2796_, 1);
v_quasiPatternApprox_2799_ = lean_ctor_get_uint8(v___x_2796_, 2);
v_constApprox_2800_ = lean_ctor_get_uint8(v___x_2796_, 3);
v_isDefEqStuckEx_2801_ = lean_ctor_get_uint8(v___x_2796_, 4);
v_unificationHints_2802_ = lean_ctor_get_uint8(v___x_2796_, 5);
v_proofIrrelevance_2803_ = lean_ctor_get_uint8(v___x_2796_, 6);
v_assignSyntheticOpaque_2804_ = lean_ctor_get_uint8(v___x_2796_, 7);
v_offsetCnstrs_2805_ = lean_ctor_get_uint8(v___x_2796_, 8);
v_transparency_2806_ = lean_ctor_get_uint8(v___x_2796_, 9);
v_univApprox_2807_ = lean_ctor_get_uint8(v___x_2796_, 11);
v_zetaUnused_2808_ = lean_ctor_get_uint8(v___x_2796_, 17);
v_canUnfoldPredicateConfig_2809_ = lean_ctor_get_uint8(v___x_2796_, 19);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2811_ = v___x_2796_;
v_isShared_2812_ = v_isSharedCheck_2823_;
goto v_resetjp_2810_;
}
else
{
lean_dec(v___x_2796_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2823_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
uint8_t v___x_2813_; uint8_t v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2817_; 
v___x_2813_ = 1;
v___x_2814_ = 0;
v___x_2815_ = 2;
if (v_isShared_2812_ == 0)
{
v___x_2817_ = v___x_2811_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 0, v_foApprox_2797_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 1, v_ctxApprox_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 2, v_quasiPatternApprox_2799_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 3, v_constApprox_2800_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 4, v_isDefEqStuckEx_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 5, v_unificationHints_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 6, v_proofIrrelevance_2803_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 7, v_assignSyntheticOpaque_2804_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 8, v_offsetCnstrs_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 9, v_transparency_2806_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 11, v_univApprox_2807_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 17, v_zetaUnused_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, 19, v_canUnfoldPredicateConfig_2809_);
v___x_2817_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
uint64_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_ctor_set_uint8(v___x_2817_, 10, v___x_2814_);
lean_ctor_set_uint8(v___x_2817_, 12, v___x_2813_);
lean_ctor_set_uint8(v___x_2817_, 13, v___x_2813_);
lean_ctor_set_uint8(v___x_2817_, 14, v___x_2815_);
lean_ctor_set_uint8(v___x_2817_, 15, v___x_2813_);
lean_ctor_set_uint8(v___x_2817_, 16, v___x_2813_);
lean_ctor_set_uint8(v___x_2817_, 18, v___x_2813_);
v___x_2818_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2817_);
v___x_2819_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set_uint64(v___x_2819_, sizeof(void*)*1, v___x_2818_);
lean_inc(v___y_2785_);
lean_inc(v___y_2795_);
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2792_);
lean_inc_ref(v___y_2791_);
lean_inc(v___y_2794_);
v___x_2820_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set(v___x_2820_, 1, v___y_2794_);
lean_ctor_set(v___x_2820_, 2, v___y_2791_);
lean_ctor_set(v___x_2820_, 3, v___y_2792_);
lean_ctor_set(v___x_2820_, 4, v___y_2787_);
lean_ctor_set(v___x_2820_, 5, v___y_2795_);
lean_ctor_set(v___x_2820_, 6, v___y_2785_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*7, v___y_2786_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*7 + 1, v___y_2789_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*7 + 2, v___y_2788_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*7 + 3, v___y_2790_);
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
v___x_2821_ = lean_apply_5(v_x_2778_, v___x_2820_, v_a_2780_, v_a_2781_, v_a_2782_, lean_box(0));
return v___x_2821_;
}
}
}
v___jp_2824_:
{
lean_object* v_keyedConfig_2826_; uint8_t v_trackZetaDelta_2827_; lean_object* v_zetaDeltaSet_2828_; lean_object* v_lctx_2829_; lean_object* v_localInstances_2830_; lean_object* v_defEqCtx_x3f_2831_; lean_object* v_synthPendingDepth_2832_; lean_object* v_customCanUnfoldPredicate_x3f_2833_; uint8_t v_univApprox_2834_; uint8_t v_inTypeClassResolution_2835_; uint8_t v_cacheInferType_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; uint8_t v_beta_2840_; 
v_keyedConfig_2826_ = lean_ctor_get(v_a_2779_, 0);
v_trackZetaDelta_2827_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7);
v_zetaDeltaSet_2828_ = lean_ctor_get(v_a_2779_, 1);
v_lctx_2829_ = lean_ctor_get(v_a_2779_, 2);
v_localInstances_2830_ = lean_ctor_get(v_a_2779_, 3);
v_defEqCtx_x3f_2831_ = lean_ctor_get(v_a_2779_, 4);
v_synthPendingDepth_2832_ = lean_ctor_get(v_a_2779_, 5);
v_customCanUnfoldPredicate_x3f_2833_ = lean_ctor_get(v_a_2779_, 6);
v_univApprox_2834_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2835_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7 + 2);
v_cacheInferType_2836_ = lean_ctor_get_uint8(v_a_2779_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2826_);
v___x_2837_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_2825_, v_keyedConfig_2826_);
lean_inc(v_customCanUnfoldPredicate_x3f_2833_);
lean_inc(v_synthPendingDepth_2832_);
lean_inc(v_defEqCtx_x3f_2831_);
lean_inc_ref(v_localInstances_2830_);
lean_inc_ref(v_lctx_2829_);
lean_inc(v_zetaDeltaSet_2828_);
v___x_2838_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v_zetaDeltaSet_2828_);
lean_ctor_set(v___x_2838_, 2, v_lctx_2829_);
lean_ctor_set(v___x_2838_, 3, v_localInstances_2830_);
lean_ctor_set(v___x_2838_, 4, v_defEqCtx_x3f_2831_);
lean_ctor_set(v___x_2838_, 5, v_synthPendingDepth_2832_);
lean_ctor_set(v___x_2838_, 6, v_customCanUnfoldPredicate_x3f_2833_);
lean_ctor_set_uint8(v___x_2838_, sizeof(void*)*7, v_trackZetaDelta_2827_);
lean_ctor_set_uint8(v___x_2838_, sizeof(void*)*7 + 1, v_univApprox_2834_);
lean_ctor_set_uint8(v___x_2838_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2835_);
lean_ctor_set_uint8(v___x_2838_, sizeof(void*)*7 + 3, v_cacheInferType_2836_);
v___x_2839_ = l_Lean_Meta_Context_config(v___x_2838_);
v_beta_2840_ = lean_ctor_get_uint8(v___x_2839_, 13);
if (v_beta_2840_ == 0)
{
lean_dec_ref(v___x_2839_);
v___y_2785_ = v_customCanUnfoldPredicate_x3f_2833_;
v___y_2786_ = v_trackZetaDelta_2827_;
v___y_2787_ = v_defEqCtx_x3f_2831_;
v___y_2788_ = v_inTypeClassResolution_2835_;
v___y_2789_ = v_univApprox_2834_;
v___y_2790_ = v_cacheInferType_2836_;
v___y_2791_ = v_lctx_2829_;
v___y_2792_ = v_localInstances_2830_;
v___y_2793_ = v___x_2838_;
v___y_2794_ = v_zetaDeltaSet_2828_;
v___y_2795_ = v_synthPendingDepth_2832_;
goto v___jp_2784_;
}
else
{
uint8_t v_iota_2841_; 
v_iota_2841_ = lean_ctor_get_uint8(v___x_2839_, 12);
if (v_iota_2841_ == 0)
{
lean_dec_ref(v___x_2839_);
v___y_2785_ = v_customCanUnfoldPredicate_x3f_2833_;
v___y_2786_ = v_trackZetaDelta_2827_;
v___y_2787_ = v_defEqCtx_x3f_2831_;
v___y_2788_ = v_inTypeClassResolution_2835_;
v___y_2789_ = v_univApprox_2834_;
v___y_2790_ = v_cacheInferType_2836_;
v___y_2791_ = v_lctx_2829_;
v___y_2792_ = v_localInstances_2830_;
v___y_2793_ = v___x_2838_;
v___y_2794_ = v_zetaDeltaSet_2828_;
v___y_2795_ = v_synthPendingDepth_2832_;
goto v___jp_2784_;
}
else
{
uint8_t v_zeta_2842_; 
v_zeta_2842_ = lean_ctor_get_uint8(v___x_2839_, 15);
if (v_zeta_2842_ == 0)
{
lean_dec_ref(v___x_2839_);
v___y_2785_ = v_customCanUnfoldPredicate_x3f_2833_;
v___y_2786_ = v_trackZetaDelta_2827_;
v___y_2787_ = v_defEqCtx_x3f_2831_;
v___y_2788_ = v_inTypeClassResolution_2835_;
v___y_2789_ = v_univApprox_2834_;
v___y_2790_ = v_cacheInferType_2836_;
v___y_2791_ = v_lctx_2829_;
v___y_2792_ = v_localInstances_2830_;
v___y_2793_ = v___x_2838_;
v___y_2794_ = v_zetaDeltaSet_2828_;
v___y_2795_ = v_synthPendingDepth_2832_;
goto v___jp_2784_;
}
else
{
uint8_t v_zetaHave_2843_; 
v_zetaHave_2843_ = lean_ctor_get_uint8(v___x_2839_, 18);
if (v_zetaHave_2843_ == 0)
{
lean_dec_ref(v___x_2839_);
v___y_2785_ = v_customCanUnfoldPredicate_x3f_2833_;
v___y_2786_ = v_trackZetaDelta_2827_;
v___y_2787_ = v_defEqCtx_x3f_2831_;
v___y_2788_ = v_inTypeClassResolution_2835_;
v___y_2789_ = v_univApprox_2834_;
v___y_2790_ = v_cacheInferType_2836_;
v___y_2791_ = v_lctx_2829_;
v___y_2792_ = v_localInstances_2830_;
v___y_2793_ = v___x_2838_;
v___y_2794_ = v_zetaDeltaSet_2828_;
v___y_2795_ = v_synthPendingDepth_2832_;
goto v___jp_2784_;
}
else
{
uint8_t v_zetaDelta_2844_; 
v_zetaDelta_2844_ = lean_ctor_get_uint8(v___x_2839_, 16);
if (v_zetaDelta_2844_ == 0)
{
lean_dec_ref(v___x_2839_);
v___y_2785_ = v_customCanUnfoldPredicate_x3f_2833_;
v___y_2786_ = v_trackZetaDelta_2827_;
v___y_2787_ = v_defEqCtx_x3f_2831_;
v___y_2788_ = v_inTypeClassResolution_2835_;
v___y_2789_ = v_univApprox_2834_;
v___y_2790_ = v_cacheInferType_2836_;
v___y_2791_ = v_lctx_2829_;
v___y_2792_ = v_localInstances_2830_;
v___y_2793_ = v___x_2838_;
v___y_2794_ = v_zetaDeltaSet_2828_;
v___y_2795_ = v_synthPendingDepth_2832_;
goto v___jp_2784_;
}
else
{
uint8_t v_etaStruct_2845_; uint8_t v_proj_2846_; uint8_t v___x_2847_; uint8_t v___x_2848_; 
v_etaStruct_2845_ = lean_ctor_get_uint8(v___x_2839_, 10);
v_proj_2846_ = lean_ctor_get_uint8(v___x_2839_, 14);
lean_dec_ref(v___x_2839_);
v___x_2847_ = 2;
v___x_2848_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
v___y_2785_ = v_customCanUnfoldPredicate_x3f_2833_;
v___y_2786_ = v_trackZetaDelta_2827_;
v___y_2787_ = v_defEqCtx_x3f_2831_;
v___y_2788_ = v_inTypeClassResolution_2835_;
v___y_2789_ = v_univApprox_2834_;
v___y_2790_ = v_cacheInferType_2836_;
v___y_2791_ = v_lctx_2829_;
v___y_2792_ = v_localInstances_2830_;
v___y_2793_ = v___x_2838_;
v___y_2794_ = v_zetaDeltaSet_2828_;
v___y_2795_ = v_synthPendingDepth_2832_;
goto v___jp_2784_;
}
else
{
uint8_t v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = 0;
v___x_2850_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2845_, v___x_2849_);
if (v___x_2850_ == 0)
{
v___y_2785_ = v_customCanUnfoldPredicate_x3f_2833_;
v___y_2786_ = v_trackZetaDelta_2827_;
v___y_2787_ = v_defEqCtx_x3f_2831_;
v___y_2788_ = v_inTypeClassResolution_2835_;
v___y_2789_ = v_univApprox_2834_;
v___y_2790_ = v_cacheInferType_2836_;
v___y_2791_ = v_lctx_2829_;
v___y_2792_ = v_localInstances_2830_;
v___y_2793_ = v___x_2838_;
v___y_2794_ = v_zetaDeltaSet_2828_;
v___y_2795_ = v_synthPendingDepth_2832_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2851_; 
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
v___x_2851_ = lean_apply_5(v_x_2778_, v___x_2838_, v_a_2780_, v_a_2781_, v_a_2782_, lean_box(0));
return v___x_2851_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2863_, lean_object* v_x_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___y_2871_; uint8_t v___y_2872_; lean_object* v___y_2873_; uint8_t v___y_2874_; uint8_t v___y_2875_; uint8_t v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; uint8_t v___y_2911_; lean_object* v___x_2938_; uint8_t v_transparency_2939_; uint8_t v___x_2940_; uint8_t v___x_2941_; 
v___x_2938_ = l_Lean_Meta_Context_config(v_a_2865_);
v_transparency_2939_ = lean_ctor_get_uint8(v___x_2938_, 9);
lean_dec_ref(v___x_2938_);
v___x_2940_ = 1;
v___x_2941_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2939_, v___x_2940_);
if (v___x_2941_ == 0)
{
v___y_2911_ = v_transparency_2939_;
goto v___jp_2910_;
}
else
{
v___y_2911_ = v___x_2940_;
goto v___jp_2910_;
}
v___jp_2870_:
{
lean_object* v___x_2882_; uint8_t v_foApprox_2883_; uint8_t v_ctxApprox_2884_; uint8_t v_quasiPatternApprox_2885_; uint8_t v_constApprox_2886_; uint8_t v_isDefEqStuckEx_2887_; uint8_t v_unificationHints_2888_; uint8_t v_proofIrrelevance_2889_; uint8_t v_assignSyntheticOpaque_2890_; uint8_t v_offsetCnstrs_2891_; uint8_t v_transparency_2892_; uint8_t v_univApprox_2893_; uint8_t v_zetaUnused_2894_; uint8_t v_canUnfoldPredicateConfig_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2909_; 
v___x_2882_ = l_Lean_Meta_Context_config(v___y_2879_);
lean_dec_ref(v___y_2879_);
v_foApprox_2883_ = lean_ctor_get_uint8(v___x_2882_, 0);
v_ctxApprox_2884_ = lean_ctor_get_uint8(v___x_2882_, 1);
v_quasiPatternApprox_2885_ = lean_ctor_get_uint8(v___x_2882_, 2);
v_constApprox_2886_ = lean_ctor_get_uint8(v___x_2882_, 3);
v_isDefEqStuckEx_2887_ = lean_ctor_get_uint8(v___x_2882_, 4);
v_unificationHints_2888_ = lean_ctor_get_uint8(v___x_2882_, 5);
v_proofIrrelevance_2889_ = lean_ctor_get_uint8(v___x_2882_, 6);
v_assignSyntheticOpaque_2890_ = lean_ctor_get_uint8(v___x_2882_, 7);
v_offsetCnstrs_2891_ = lean_ctor_get_uint8(v___x_2882_, 8);
v_transparency_2892_ = lean_ctor_get_uint8(v___x_2882_, 9);
v_univApprox_2893_ = lean_ctor_get_uint8(v___x_2882_, 11);
v_zetaUnused_2894_ = lean_ctor_get_uint8(v___x_2882_, 17);
v_canUnfoldPredicateConfig_2895_ = lean_ctor_get_uint8(v___x_2882_, 19);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2897_ = v___x_2882_;
v_isShared_2898_ = v_isSharedCheck_2909_;
goto v_resetjp_2896_;
}
else
{
lean_dec(v___x_2882_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2909_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
uint8_t v___x_2899_; uint8_t v___x_2900_; uint8_t v___x_2901_; lean_object* v___x_2903_; 
v___x_2899_ = 1;
v___x_2900_ = 0;
v___x_2901_ = 2;
if (v_isShared_2898_ == 0)
{
v___x_2903_ = v___x_2897_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 0, v_foApprox_2883_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 1, v_ctxApprox_2884_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 2, v_quasiPatternApprox_2885_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 3, v_constApprox_2886_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 4, v_isDefEqStuckEx_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 5, v_unificationHints_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 6, v_proofIrrelevance_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 7, v_assignSyntheticOpaque_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 8, v_offsetCnstrs_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 9, v_transparency_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 11, v_univApprox_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 17, v_zetaUnused_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, 19, v_canUnfoldPredicateConfig_2895_);
v___x_2903_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
uint64_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_ctor_set_uint8(v___x_2903_, 10, v___x_2900_);
lean_ctor_set_uint8(v___x_2903_, 12, v___x_2899_);
lean_ctor_set_uint8(v___x_2903_, 13, v___x_2899_);
lean_ctor_set_uint8(v___x_2903_, 14, v___x_2901_);
lean_ctor_set_uint8(v___x_2903_, 15, v___x_2899_);
lean_ctor_set_uint8(v___x_2903_, 16, v___x_2899_);
lean_ctor_set_uint8(v___x_2903_, 18, v___x_2899_);
v___x_2904_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set_uint64(v___x_2905_, sizeof(void*)*1, v___x_2904_);
lean_inc(v___y_2871_);
lean_inc(v___y_2881_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2878_);
lean_inc_ref(v___y_2877_);
lean_inc(v___y_2880_);
v___x_2906_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v___y_2880_);
lean_ctor_set(v___x_2906_, 2, v___y_2877_);
lean_ctor_set(v___x_2906_, 3, v___y_2878_);
lean_ctor_set(v___x_2906_, 4, v___y_2873_);
lean_ctor_set(v___x_2906_, 5, v___y_2881_);
lean_ctor_set(v___x_2906_, 6, v___y_2871_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*7, v___y_2872_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*7 + 1, v___y_2875_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*7 + 2, v___y_2874_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*7 + 3, v___y_2876_);
lean_inc(v_a_2868_);
lean_inc_ref(v_a_2867_);
lean_inc(v_a_2866_);
v___x_2907_ = lean_apply_5(v_x_2864_, v___x_2906_, v_a_2866_, v_a_2867_, v_a_2868_, lean_box(0));
return v___x_2907_;
}
}
}
v___jp_2910_:
{
lean_object* v_keyedConfig_2912_; uint8_t v_trackZetaDelta_2913_; lean_object* v_zetaDeltaSet_2914_; lean_object* v_lctx_2915_; lean_object* v_localInstances_2916_; lean_object* v_defEqCtx_x3f_2917_; lean_object* v_synthPendingDepth_2918_; lean_object* v_customCanUnfoldPredicate_x3f_2919_; uint8_t v_univApprox_2920_; uint8_t v_inTypeClassResolution_2921_; uint8_t v_cacheInferType_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v_beta_2926_; 
v_keyedConfig_2912_ = lean_ctor_get(v_a_2865_, 0);
v_trackZetaDelta_2913_ = lean_ctor_get_uint8(v_a_2865_, sizeof(void*)*7);
v_zetaDeltaSet_2914_ = lean_ctor_get(v_a_2865_, 1);
v_lctx_2915_ = lean_ctor_get(v_a_2865_, 2);
v_localInstances_2916_ = lean_ctor_get(v_a_2865_, 3);
v_defEqCtx_x3f_2917_ = lean_ctor_get(v_a_2865_, 4);
v_synthPendingDepth_2918_ = lean_ctor_get(v_a_2865_, 5);
v_customCanUnfoldPredicate_x3f_2919_ = lean_ctor_get(v_a_2865_, 6);
v_univApprox_2920_ = lean_ctor_get_uint8(v_a_2865_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2921_ = lean_ctor_get_uint8(v_a_2865_, sizeof(void*)*7 + 2);
v_cacheInferType_2922_ = lean_ctor_get_uint8(v_a_2865_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2912_);
v___x_2923_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_2911_, v_keyedConfig_2912_);
lean_inc(v_customCanUnfoldPredicate_x3f_2919_);
lean_inc(v_synthPendingDepth_2918_);
lean_inc(v_defEqCtx_x3f_2917_);
lean_inc_ref(v_localInstances_2916_);
lean_inc_ref(v_lctx_2915_);
lean_inc(v_zetaDeltaSet_2914_);
v___x_2924_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v_zetaDeltaSet_2914_);
lean_ctor_set(v___x_2924_, 2, v_lctx_2915_);
lean_ctor_set(v___x_2924_, 3, v_localInstances_2916_);
lean_ctor_set(v___x_2924_, 4, v_defEqCtx_x3f_2917_);
lean_ctor_set(v___x_2924_, 5, v_synthPendingDepth_2918_);
lean_ctor_set(v___x_2924_, 6, v_customCanUnfoldPredicate_x3f_2919_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7, v_trackZetaDelta_2913_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7 + 1, v_univApprox_2920_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2921_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*7 + 3, v_cacheInferType_2922_);
v___x_2925_ = l_Lean_Meta_Context_config(v___x_2924_);
v_beta_2926_ = lean_ctor_get_uint8(v___x_2925_, 13);
if (v_beta_2926_ == 0)
{
lean_dec_ref(v___x_2925_);
v___y_2871_ = v_customCanUnfoldPredicate_x3f_2919_;
v___y_2872_ = v_trackZetaDelta_2913_;
v___y_2873_ = v_defEqCtx_x3f_2917_;
v___y_2874_ = v_inTypeClassResolution_2921_;
v___y_2875_ = v_univApprox_2920_;
v___y_2876_ = v_cacheInferType_2922_;
v___y_2877_ = v_lctx_2915_;
v___y_2878_ = v_localInstances_2916_;
v___y_2879_ = v___x_2924_;
v___y_2880_ = v_zetaDeltaSet_2914_;
v___y_2881_ = v_synthPendingDepth_2918_;
goto v___jp_2870_;
}
else
{
uint8_t v_iota_2927_; 
v_iota_2927_ = lean_ctor_get_uint8(v___x_2925_, 12);
if (v_iota_2927_ == 0)
{
lean_dec_ref(v___x_2925_);
v___y_2871_ = v_customCanUnfoldPredicate_x3f_2919_;
v___y_2872_ = v_trackZetaDelta_2913_;
v___y_2873_ = v_defEqCtx_x3f_2917_;
v___y_2874_ = v_inTypeClassResolution_2921_;
v___y_2875_ = v_univApprox_2920_;
v___y_2876_ = v_cacheInferType_2922_;
v___y_2877_ = v_lctx_2915_;
v___y_2878_ = v_localInstances_2916_;
v___y_2879_ = v___x_2924_;
v___y_2880_ = v_zetaDeltaSet_2914_;
v___y_2881_ = v_synthPendingDepth_2918_;
goto v___jp_2870_;
}
else
{
uint8_t v_zeta_2928_; 
v_zeta_2928_ = lean_ctor_get_uint8(v___x_2925_, 15);
if (v_zeta_2928_ == 0)
{
lean_dec_ref(v___x_2925_);
v___y_2871_ = v_customCanUnfoldPredicate_x3f_2919_;
v___y_2872_ = v_trackZetaDelta_2913_;
v___y_2873_ = v_defEqCtx_x3f_2917_;
v___y_2874_ = v_inTypeClassResolution_2921_;
v___y_2875_ = v_univApprox_2920_;
v___y_2876_ = v_cacheInferType_2922_;
v___y_2877_ = v_lctx_2915_;
v___y_2878_ = v_localInstances_2916_;
v___y_2879_ = v___x_2924_;
v___y_2880_ = v_zetaDeltaSet_2914_;
v___y_2881_ = v_synthPendingDepth_2918_;
goto v___jp_2870_;
}
else
{
uint8_t v_zetaHave_2929_; 
v_zetaHave_2929_ = lean_ctor_get_uint8(v___x_2925_, 18);
if (v_zetaHave_2929_ == 0)
{
lean_dec_ref(v___x_2925_);
v___y_2871_ = v_customCanUnfoldPredicate_x3f_2919_;
v___y_2872_ = v_trackZetaDelta_2913_;
v___y_2873_ = v_defEqCtx_x3f_2917_;
v___y_2874_ = v_inTypeClassResolution_2921_;
v___y_2875_ = v_univApprox_2920_;
v___y_2876_ = v_cacheInferType_2922_;
v___y_2877_ = v_lctx_2915_;
v___y_2878_ = v_localInstances_2916_;
v___y_2879_ = v___x_2924_;
v___y_2880_ = v_zetaDeltaSet_2914_;
v___y_2881_ = v_synthPendingDepth_2918_;
goto v___jp_2870_;
}
else
{
uint8_t v_zetaDelta_2930_; 
v_zetaDelta_2930_ = lean_ctor_get_uint8(v___x_2925_, 16);
if (v_zetaDelta_2930_ == 0)
{
lean_dec_ref(v___x_2925_);
v___y_2871_ = v_customCanUnfoldPredicate_x3f_2919_;
v___y_2872_ = v_trackZetaDelta_2913_;
v___y_2873_ = v_defEqCtx_x3f_2917_;
v___y_2874_ = v_inTypeClassResolution_2921_;
v___y_2875_ = v_univApprox_2920_;
v___y_2876_ = v_cacheInferType_2922_;
v___y_2877_ = v_lctx_2915_;
v___y_2878_ = v_localInstances_2916_;
v___y_2879_ = v___x_2924_;
v___y_2880_ = v_zetaDeltaSet_2914_;
v___y_2881_ = v_synthPendingDepth_2918_;
goto v___jp_2870_;
}
else
{
uint8_t v_etaStruct_2931_; uint8_t v_proj_2932_; uint8_t v___x_2933_; uint8_t v___x_2934_; 
v_etaStruct_2931_ = lean_ctor_get_uint8(v___x_2925_, 10);
v_proj_2932_ = lean_ctor_get_uint8(v___x_2925_, 14);
lean_dec_ref(v___x_2925_);
v___x_2933_ = 2;
v___x_2934_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
v___y_2871_ = v_customCanUnfoldPredicate_x3f_2919_;
v___y_2872_ = v_trackZetaDelta_2913_;
v___y_2873_ = v_defEqCtx_x3f_2917_;
v___y_2874_ = v_inTypeClassResolution_2921_;
v___y_2875_ = v_univApprox_2920_;
v___y_2876_ = v_cacheInferType_2922_;
v___y_2877_ = v_lctx_2915_;
v___y_2878_ = v_localInstances_2916_;
v___y_2879_ = v___x_2924_;
v___y_2880_ = v_zetaDeltaSet_2914_;
v___y_2881_ = v_synthPendingDepth_2918_;
goto v___jp_2870_;
}
else
{
uint8_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = 0;
v___x_2936_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2931_, v___x_2935_);
if (v___x_2936_ == 0)
{
v___y_2871_ = v_customCanUnfoldPredicate_x3f_2919_;
v___y_2872_ = v_trackZetaDelta_2913_;
v___y_2873_ = v_defEqCtx_x3f_2917_;
v___y_2874_ = v_inTypeClassResolution_2921_;
v___y_2875_ = v_univApprox_2920_;
v___y_2876_ = v_cacheInferType_2922_;
v___y_2877_ = v_lctx_2915_;
v___y_2878_ = v_localInstances_2916_;
v___y_2879_ = v___x_2924_;
v___y_2880_ = v_zetaDeltaSet_2914_;
v___y_2881_ = v_synthPendingDepth_2918_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2937_; 
lean_inc(v_a_2868_);
lean_inc_ref(v_a_2867_);
lean_inc(v_a_2866_);
v___x_2937_ = lean_apply_5(v_x_2864_, v___x_2924_, v_a_2866_, v_a_2867_, v_a_2868_, lean_box(0));
return v___x_2937_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_x_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2942_, v_x_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
return v_res_2949_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_box(0);
v___x_2951_ = l_Lean_interruptExceptionId;
v___x_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___x_2950_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2968_, lean_object* v_x_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
lean_object* v_ks_2972_; lean_object* v_vs_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3002_; 
v_ks_2972_ = lean_ctor_get(v_x_2968_, 0);
v_vs_2973_ = lean_ctor_get(v_x_2968_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_x_2968_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2975_ = v_x_2968_;
v_isShared_2976_ = v_isSharedCheck_3002_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_vs_2973_);
lean_inc(v_ks_2972_);
lean_dec(v_x_2968_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3002_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
uint8_t v___y_2978_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = lean_array_get_size(v_ks_2972_);
v___x_2991_ = lean_nat_dec_lt(v_x_2969_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_del_object(v___x_2975_);
lean_dec(v_x_2969_);
v___x_2992_ = lean_array_push(v_ks_2972_, v_x_2970_);
v___x_2993_ = lean_array_push(v_vs_2973_, v_x_2971_);
v___x_2994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
return v___x_2994_;
}
else
{
lean_object* v_expr_2995_; uint64_t v_configKey_2996_; lean_object* v_k_x27_2997_; lean_object* v_expr_2998_; uint64_t v_configKey_2999_; uint8_t v___x_3000_; 
v_expr_2995_ = lean_ctor_get(v_x_2970_, 0);
v_configKey_2996_ = lean_ctor_get_uint64(v_x_2970_, sizeof(void*)*1);
v_k_x27_2997_ = lean_array_fget_borrowed(v_ks_2972_, v_x_2969_);
v_expr_2998_ = lean_ctor_get(v_k_x27_2997_, 0);
v_configKey_2999_ = lean_ctor_get_uint64(v_k_x27_2997_, sizeof(void*)*1);
v___x_3000_ = lean_expr_equal(v_expr_2995_, v_expr_2998_);
if (v___x_3000_ == 0)
{
v___y_2978_ = v___x_3000_;
goto v___jp_2977_;
}
else
{
uint8_t v___x_3001_; 
v___x_3001_ = lean_uint64_dec_eq(v_configKey_2996_, v_configKey_2999_);
v___y_2978_ = v___x_3001_;
goto v___jp_2977_;
}
}
v___jp_2977_:
{
if (v___y_2978_ == 0)
{
lean_object* v___x_2980_; 
if (v_isShared_2976_ == 0)
{
v___x_2980_ = v___x_2975_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_ks_2972_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_vs_2973_);
v___x_2980_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = lean_unsigned_to_nat(1u);
v___x_2982_ = lean_nat_add(v_x_2969_, v___x_2981_);
lean_dec(v_x_2969_);
v_x_2968_ = v___x_2980_;
v_x_2969_ = v___x_2982_;
goto _start;
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2985_ = lean_array_fset(v_ks_2972_, v_x_2969_, v_x_2970_);
v___x_2986_ = lean_array_fset(v_vs_2973_, v_x_2969_, v_x_2971_);
lean_dec(v_x_2969_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 1, v___x_2986_);
lean_ctor_set(v___x_2975_, 0, v___x_2985_);
v___x_2988_ = v___x_2975_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v___x_2986_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_3003_, lean_object* v_k_3004_, lean_object* v_v_3005_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_3003_, v___x_3006_, v_k_3004_, v_v_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_3009_, size_t v_x_3010_, size_t v_x_3011_, lean_object* v_x_3012_, lean_object* v_x_3013_){
_start:
{
if (lean_obj_tag(v_x_3009_) == 0)
{
lean_object* v_es_3014_; size_t v___x_3015_; size_t v___x_3016_; lean_object* v_j_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_es_3014_ = lean_ctor_get(v_x_3009_, 0);
v___x_3015_ = ((size_t)31ULL);
v___x_3016_ = lean_usize_land(v_x_3010_, v___x_3015_);
v_j_3017_ = lean_usize_to_nat(v___x_3016_);
v___x_3018_ = lean_array_get_size(v_es_3014_);
v___x_3019_ = lean_nat_dec_lt(v_j_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_dec(v_j_3017_);
lean_dec(v_x_3013_);
lean_dec_ref(v_x_3012_);
return v_x_3009_;
}
else
{
lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3065_; 
lean_inc_ref(v_es_3014_);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_x_3009_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v_x_3009_, 0);
lean_dec(v_unused_3066_);
v___x_3021_ = v_x_3009_;
v_isShared_3022_ = v_isSharedCheck_3065_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v_x_3009_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3065_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_v_3023_; lean_object* v___x_3024_; lean_object* v_xs_x27_3025_; lean_object* v___y_3027_; 
v_v_3023_ = lean_array_fget(v_es_3014_, v_j_3017_);
v___x_3024_ = lean_box(0);
v_xs_x27_3025_ = lean_array_fset(v_es_3014_, v_j_3017_, v___x_3024_);
switch(lean_obj_tag(v_v_3023_))
{
case 0:
{
lean_object* v_key_3032_; lean_object* v_val_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3050_; 
v_key_3032_ = lean_ctor_get(v_v_3023_, 0);
v_val_3033_ = lean_ctor_get(v_v_3023_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_v_3023_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3035_ = v_v_3023_;
v_isShared_3036_ = v_isSharedCheck_3050_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_val_3033_);
lean_inc(v_key_3032_);
lean_dec(v_v_3023_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3050_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
uint8_t v___y_3038_; lean_object* v_expr_3044_; uint64_t v_configKey_3045_; lean_object* v_expr_3046_; uint64_t v_configKey_3047_; uint8_t v___x_3048_; 
v_expr_3044_ = lean_ctor_get(v_x_3012_, 0);
v_configKey_3045_ = lean_ctor_get_uint64(v_x_3012_, sizeof(void*)*1);
v_expr_3046_ = lean_ctor_get(v_key_3032_, 0);
v_configKey_3047_ = lean_ctor_get_uint64(v_key_3032_, sizeof(void*)*1);
v___x_3048_ = lean_expr_equal(v_expr_3044_, v_expr_3046_);
if (v___x_3048_ == 0)
{
v___y_3038_ = v___x_3048_;
goto v___jp_3037_;
}
else
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_uint64_dec_eq(v_configKey_3045_, v_configKey_3047_);
v___y_3038_ = v___x_3049_;
goto v___jp_3037_;
}
v___jp_3037_:
{
if (v___y_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_del_object(v___x_3035_);
v___x_3039_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3032_, v_val_3033_, v_x_3012_, v_x_3013_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
v___y_3027_ = v___x_3040_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3042_; 
lean_dec(v_val_3033_);
lean_dec(v_key_3032_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v_x_3013_);
lean_ctor_set(v___x_3035_, 0, v_x_3012_);
v___x_3042_ = v___x_3035_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_x_3012_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v_x_3013_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
v___y_3027_ = v___x_3042_;
goto v___jp_3026_;
}
}
}
}
}
case 1:
{
lean_object* v_node_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3063_; 
v_node_3051_ = lean_ctor_get(v_v_3023_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_v_3023_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3053_ = v_v_3023_;
v_isShared_3054_ = v_isSharedCheck_3063_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_node_3051_);
lean_dec(v_v_3023_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3063_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
size_t v___x_3055_; size_t v___x_3056_; size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3055_ = ((size_t)5ULL);
v___x_3056_ = lean_usize_shift_right(v_x_3010_, v___x_3055_);
v___x_3057_ = ((size_t)1ULL);
v___x_3058_ = lean_usize_add(v_x_3011_, v___x_3057_);
v___x_3059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_3051_, v___x_3056_, v___x_3058_, v_x_3012_, v_x_3013_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3059_);
v___x_3061_ = v___x_3053_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
v___y_3027_ = v___x_3061_;
goto v___jp_3026_;
}
}
}
default: 
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v_x_3012_);
lean_ctor_set(v___x_3064_, 1, v_x_3013_);
v___y_3027_ = v___x_3064_;
goto v___jp_3026_;
}
}
v___jp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_array_fset(v_xs_x27_3025_, v_j_3017_, v___y_3027_);
lean_dec(v_j_3017_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3028_);
v___x_3030_ = v___x_3021_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
else
{
lean_object* v_ks_3067_; lean_object* v_vs_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3088_; 
v_ks_3067_ = lean_ctor_get(v_x_3009_, 0);
v_vs_3068_ = lean_ctor_get(v_x_3009_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_x_3009_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3070_ = v_x_3009_;
v_isShared_3071_ = v_isSharedCheck_3088_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_vs_3068_);
lean_inc(v_ks_3067_);
lean_dec(v_x_3009_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3088_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_ks_3067_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_vs_3068_);
v___x_3073_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v_newNode_3074_; uint8_t v___y_3076_; size_t v___x_3082_; uint8_t v___x_3083_; 
v_newNode_3074_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_3073_, v_x_3012_, v_x_3013_);
v___x_3082_ = ((size_t)7ULL);
v___x_3083_ = lean_usize_dec_le(v___x_3082_, v_x_3011_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3084_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3074_);
v___x_3085_ = lean_unsigned_to_nat(4u);
v___x_3086_ = lean_nat_dec_lt(v___x_3084_, v___x_3085_);
lean_dec(v___x_3084_);
v___y_3076_ = v___x_3086_;
goto v___jp_3075_;
}
else
{
v___y_3076_ = v___x_3083_;
goto v___jp_3075_;
}
v___jp_3075_:
{
if (v___y_3076_ == 0)
{
lean_object* v_ks_3077_; lean_object* v_vs_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v_ks_3077_ = lean_ctor_get(v_newNode_3074_, 0);
lean_inc_ref(v_ks_3077_);
v_vs_3078_ = lean_ctor_get(v_newNode_3074_, 1);
lean_inc_ref(v_vs_3078_);
lean_dec_ref(v_newNode_3074_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_3081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_3011_, v_ks_3077_, v_vs_3078_, v___x_3079_, v___x_3080_);
lean_dec_ref(v_vs_3078_);
lean_dec_ref(v_ks_3077_);
return v___x_3081_;
}
else
{
return v_newNode_3074_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_3089_, lean_object* v_keys_3090_, lean_object* v_vals_3091_, lean_object* v_i_3092_, lean_object* v_entries_3093_){
_start:
{
lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3094_ = lean_array_get_size(v_keys_3090_);
v___x_3095_ = lean_nat_dec_lt(v_i_3092_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_dec(v_i_3092_);
return v_entries_3093_;
}
else
{
lean_object* v_k_3096_; lean_object* v_expr_3097_; uint64_t v_configKey_3098_; lean_object* v_v_3099_; uint64_t v___x_3100_; uint64_t v___x_3101_; size_t v_h_3102_; size_t v___x_3103_; lean_object* v___x_3104_; size_t v___x_3105_; size_t v___x_3106_; size_t v___x_3107_; size_t v_h_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_k_3096_ = lean_array_fget_borrowed(v_keys_3090_, v_i_3092_);
v_expr_3097_ = lean_ctor_get(v_k_3096_, 0);
v_configKey_3098_ = lean_ctor_get_uint64(v_k_3096_, sizeof(void*)*1);
v_v_3099_ = lean_array_fget_borrowed(v_vals_3091_, v_i_3092_);
v___x_3100_ = l_Lean_Expr_hash(v_expr_3097_);
v___x_3101_ = lean_uint64_mix_hash(v___x_3100_, v_configKey_3098_);
v_h_3102_ = lean_uint64_to_usize(v___x_3101_);
v___x_3103_ = ((size_t)5ULL);
v___x_3104_ = lean_unsigned_to_nat(1u);
v___x_3105_ = ((size_t)1ULL);
v___x_3106_ = lean_usize_sub(v_depth_3089_, v___x_3105_);
v___x_3107_ = lean_usize_mul(v___x_3103_, v___x_3106_);
v_h_3108_ = lean_usize_shift_right(v_h_3102_, v___x_3107_);
v___x_3109_ = lean_nat_add(v_i_3092_, v___x_3104_);
lean_dec(v_i_3092_);
lean_inc(v_v_3099_);
lean_inc(v_k_3096_);
v___x_3110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_3093_, v_h_3108_, v_depth_3089_, v_k_3096_, v_v_3099_);
v_i_3092_ = v___x_3109_;
v_entries_3093_ = v___x_3110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3112_, lean_object* v_keys_3113_, lean_object* v_vals_3114_, lean_object* v_i_3115_, lean_object* v_entries_3116_){
_start:
{
size_t v_depth_boxed_3117_; lean_object* v_res_3118_; 
v_depth_boxed_3117_ = lean_unbox_usize(v_depth_3112_);
lean_dec(v_depth_3112_);
v_res_3118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_3117_, v_keys_3113_, v_vals_3114_, v_i_3115_, v_entries_3116_);
lean_dec_ref(v_vals_3114_);
lean_dec_ref(v_keys_3113_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_, lean_object* v_x_3122_, lean_object* v_x_3123_){
_start:
{
size_t v_x_2762__boxed_3124_; size_t v_x_2763__boxed_3125_; lean_object* v_res_3126_; 
v_x_2762__boxed_3124_ = lean_unbox_usize(v_x_3120_);
lean_dec(v_x_3120_);
v_x_2763__boxed_3125_ = lean_unbox_usize(v_x_3121_);
lean_dec(v_x_3121_);
v_res_3126_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3119_, v_x_2762__boxed_3124_, v_x_2763__boxed_3125_, v_x_3122_, v_x_3123_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_3127_, lean_object* v_x_3128_, lean_object* v_x_3129_){
_start:
{
lean_object* v_expr_3130_; uint64_t v_configKey_3131_; uint64_t v___x_3132_; uint64_t v___x_3133_; size_t v___x_3134_; size_t v___x_3135_; lean_object* v___x_3136_; 
v_expr_3130_ = lean_ctor_get(v_x_3128_, 0);
v_configKey_3131_ = lean_ctor_get_uint64(v_x_3128_, sizeof(void*)*1);
v___x_3132_ = l_Lean_Expr_hash(v_expr_3130_);
v___x_3133_ = lean_uint64_mix_hash(v___x_3132_, v_configKey_3131_);
v___x_3134_ = lean_uint64_to_usize(v___x_3133_);
v___x_3135_ = ((size_t)1ULL);
v___x_3136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3127_, v___x_3134_, v___x_3135_, v_x_3128_, v_x_3129_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_3137_, lean_object* v_vals_3138_, lean_object* v_i_3139_, lean_object* v_k_3140_){
_start:
{
uint8_t v___y_3142_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v___x_3148_ = lean_array_get_size(v_keys_3137_);
v___x_3149_ = lean_nat_dec_lt(v_i_3139_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
lean_dec(v_i_3139_);
v___x_3150_ = lean_box(0);
return v___x_3150_;
}
else
{
lean_object* v_expr_3151_; uint64_t v_configKey_3152_; lean_object* v_k_x27_3153_; lean_object* v_expr_3154_; uint64_t v_configKey_3155_; uint8_t v___x_3156_; 
v_expr_3151_ = lean_ctor_get(v_k_3140_, 0);
v_configKey_3152_ = lean_ctor_get_uint64(v_k_3140_, sizeof(void*)*1);
v_k_x27_3153_ = lean_array_fget_borrowed(v_keys_3137_, v_i_3139_);
v_expr_3154_ = lean_ctor_get(v_k_x27_3153_, 0);
v_configKey_3155_ = lean_ctor_get_uint64(v_k_x27_3153_, sizeof(void*)*1);
v___x_3156_ = lean_expr_equal(v_expr_3151_, v_expr_3154_);
if (v___x_3156_ == 0)
{
v___y_3142_ = v___x_3156_;
goto v___jp_3141_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_uint64_dec_eq(v_configKey_3152_, v_configKey_3155_);
v___y_3142_ = v___x_3157_;
goto v___jp_3141_;
}
}
v___jp_3141_:
{
if (v___y_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_unsigned_to_nat(1u);
v___x_3144_ = lean_nat_add(v_i_3139_, v___x_3143_);
lean_dec(v_i_3139_);
v_i_3139_ = v___x_3144_;
goto _start;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_array_fget_borrowed(v_vals_3138_, v_i_3139_);
lean_dec(v_i_3139_);
lean_inc(v___x_3146_);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
return v___x_3147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_3158_, lean_object* v_vals_3159_, lean_object* v_i_3160_, lean_object* v_k_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3158_, v_vals_3159_, v_i_3160_, v_k_3161_);
lean_dec_ref(v_k_3161_);
lean_dec_ref(v_vals_3159_);
lean_dec_ref(v_keys_3158_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_3163_, size_t v_x_3164_, lean_object* v_x_3165_){
_start:
{
if (lean_obj_tag(v_x_3163_) == 0)
{
lean_object* v_es_3166_; lean_object* v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; lean_object* v_j_3170_; lean_object* v___x_3171_; 
v_es_3166_ = lean_ctor_get(v_x_3163_, 0);
v___x_3167_ = lean_box(2);
v___x_3168_ = ((size_t)31ULL);
v___x_3169_ = lean_usize_land(v_x_3164_, v___x_3168_);
v_j_3170_ = lean_usize_to_nat(v___x_3169_);
v___x_3171_ = lean_array_get_borrowed(v___x_3167_, v_es_3166_, v_j_3170_);
lean_dec(v_j_3170_);
switch(lean_obj_tag(v___x_3171_))
{
case 0:
{
lean_object* v_key_3172_; lean_object* v_val_3173_; uint8_t v___y_3175_; lean_object* v_expr_3178_; uint64_t v_configKey_3179_; lean_object* v_expr_3180_; uint64_t v_configKey_3181_; uint8_t v___x_3182_; 
v_key_3172_ = lean_ctor_get(v___x_3171_, 0);
v_val_3173_ = lean_ctor_get(v___x_3171_, 1);
v_expr_3178_ = lean_ctor_get(v_x_3165_, 0);
v_configKey_3179_ = lean_ctor_get_uint64(v_x_3165_, sizeof(void*)*1);
v_expr_3180_ = lean_ctor_get(v_key_3172_, 0);
v_configKey_3181_ = lean_ctor_get_uint64(v_key_3172_, sizeof(void*)*1);
v___x_3182_ = lean_expr_equal(v_expr_3178_, v_expr_3180_);
if (v___x_3182_ == 0)
{
v___y_3175_ = v___x_3182_;
goto v___jp_3174_;
}
else
{
uint8_t v___x_3183_; 
v___x_3183_ = lean_uint64_dec_eq(v_configKey_3179_, v_configKey_3181_);
v___y_3175_ = v___x_3183_;
goto v___jp_3174_;
}
v___jp_3174_:
{
if (v___y_3175_ == 0)
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_box(0);
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; 
lean_inc(v_val_3173_);
v___x_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_val_3173_);
return v___x_3177_;
}
}
}
case 1:
{
lean_object* v_node_3184_; size_t v___x_3185_; size_t v___x_3186_; 
v_node_3184_ = lean_ctor_get(v___x_3171_, 0);
v___x_3185_ = ((size_t)5ULL);
v___x_3186_ = lean_usize_shift_right(v_x_3164_, v___x_3185_);
v_x_3163_ = v_node_3184_;
v_x_3164_ = v___x_3186_;
goto _start;
}
default: 
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_box(0);
return v___x_3188_;
}
}
}
else
{
lean_object* v_ks_3189_; lean_object* v_vs_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_ks_3189_ = lean_ctor_get(v_x_3163_, 0);
v_vs_3190_ = lean_ctor_get(v_x_3163_, 1);
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_3189_, v_vs_3190_, v___x_3191_, v_x_3165_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
size_t v_x_2971__boxed_3196_; lean_object* v_res_3197_; 
v_x_2971__boxed_3196_ = lean_unbox_usize(v_x_3194_);
lean_dec(v_x_3194_);
v_res_3197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3193_, v_x_2971__boxed_3196_, v_x_3195_);
lean_dec_ref(v_x_3195_);
lean_dec_ref(v_x_3193_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v_expr_3200_; uint64_t v_configKey_3201_; uint64_t v___x_3202_; uint64_t v___x_3203_; size_t v___x_3204_; lean_object* v___x_3205_; 
v_expr_3200_ = lean_ctor_get(v_x_3199_, 0);
v_configKey_3201_ = lean_ctor_get_uint64(v_x_3199_, sizeof(void*)*1);
v___x_3202_ = l_Lean_Expr_hash(v_expr_3200_);
v___x_3203_ = lean_uint64_mix_hash(v___x_3202_, v_configKey_3201_);
v___x_3204_ = lean_uint64_to_usize(v___x_3203_);
v___x_3205_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3198_, v___x_3204_, v_x_3199_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3206_, v_x_3207_);
lean_dec_ref(v_x_3207_);
lean_dec_ref(v_x_3206_);
return v_res_3208_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3211_ = l_Lean_stringToMessageData(v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
switch(lean_obj_tag(v_e_3212_))
{
case 0:
{
lean_object* v_deBruijnIndex_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_deBruijnIndex_3248_ = lean_ctor_get(v_e_3212_, 0);
lean_inc(v_deBruijnIndex_3248_);
lean_dec_ref_known(v_e_3212_, 1);
v___x_3249_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3250_ = l_Lean_mkBVar(v_deBruijnIndex_3248_);
v___x_3251_ = l_Lean_MessageData_ofExpr(v___x_3250_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3249_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3252_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3253_;
}
case 1:
{
lean_object* v_fvarId_3254_; lean_object* v___x_3255_; 
v_fvarId_3254_ = lean_ctor_get(v_e_3212_, 0);
lean_inc(v_fvarId_3254_);
lean_dec_ref_known(v_e_3212_, 1);
v___x_3255_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3254_, v_a_3213_, v_a_3215_, v_a_3216_);
return v___x_3255_;
}
case 2:
{
lean_object* v_mvarId_3256_; lean_object* v___x_3257_; 
v_mvarId_3256_ = lean_ctor_get(v_e_3212_, 0);
lean_inc(v_mvarId_3256_);
lean_dec_ref_known(v_e_3212_, 1);
v___x_3257_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3256_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3257_;
}
case 3:
{
lean_object* v_u_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_u_3258_ = lean_ctor_get(v_e_3212_, 0);
lean_inc(v_u_3258_);
lean_dec_ref_known(v_e_3212_, 1);
v___x_3259_ = l_Lean_Level_succ___override(v_u_3258_);
v___x_3260_ = l_Lean_mkSort(v___x_3259_);
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
return v___x_3261_;
}
case 4:
{
lean_object* v_declName_3262_; lean_object* v_us_3263_; 
v_declName_3262_ = lean_ctor_get(v_e_3212_, 0);
lean_inc(v_declName_3262_);
v_us_3263_ = lean_ctor_get(v_e_3212_, 1);
lean_inc(v_us_3263_);
if (lean_obj_tag(v_us_3263_) == 0)
{
lean_object* v___x_3279_; 
lean_dec_ref_known(v_e_3212_, 2);
v___x_3279_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3262_, v_us_3263_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3279_;
}
else
{
uint8_t v_cacheInferType_3280_; 
v_cacheInferType_3280_ = lean_ctor_get_uint8(v_a_3213_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3280_ == 0)
{
lean_dec_ref_known(v_e_3212_, 2);
goto v___jp_3264_;
}
else
{
uint8_t v___x_3281_; 
v___x_3281_ = l_Lean_Expr_hasMVar(v_e_3212_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3347_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3347_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3347_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3327_; lean_object* v_cache_3328_; lean_object* v_inferType_3329_; lean_object* v___x_3330_; 
v___x_3327_ = lean_st_ref_get(v_a_3214_);
v_cache_3328_ = lean_ctor_get(v___x_3327_, 1);
lean_inc_ref(v_cache_3328_);
lean_dec(v___x_3327_);
v_inferType_3329_ = lean_ctor_get(v_cache_3328_, 0);
lean_inc_ref(v_inferType_3329_);
lean_dec_ref(v_cache_3328_);
v___x_3330_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3329_, v_a_3283_);
lean_dec_ref(v_inferType_3329_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_cancelTk_x3f_3331_; 
lean_del_object(v___x_3285_);
v_cancelTk_x3f_3331_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3331_) == 1)
{
lean_object* v_val_3332_; uint8_t v___x_3333_; 
v_val_3332_ = lean_ctor_get(v_cancelTk_x3f_3331_, 0);
v___x_3333_ = l_IO_CancelToken_isSet(v_val_3332_);
if (v___x_3333_ == 0)
{
goto v___jp_3287_;
}
else
{
lean_object* v___x_3334_; lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3283_);
lean_dec(v_us_3263_);
lean_dec(v_declName_3262_);
v___x_3334_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
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
goto v___jp_3287_;
}
}
else
{
lean_object* v_val_3343_; lean_object* v___x_3345_; 
lean_dec(v_a_3283_);
lean_dec(v_us_3263_);
lean_dec(v_declName_3262_);
v_val_3343_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3330_, 1);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v_val_3343_);
v___x_3345_ = v___x_3285_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_val_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
v___jp_3287_:
{
lean_object* v___x_3288_; 
v___x_3288_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3262_, v_us_3263_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; uint8_t v___x_3290_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
v___x_3290_ = l_Lean_Expr_hasMVar(v_a_3289_);
if (v___x_3290_ == 0)
{
lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3325_; 
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; 
v_unused_3326_ = lean_ctor_get(v___x_3288_, 0);
lean_dec(v_unused_3326_);
v___x_3292_ = v___x_3288_;
v_isShared_3293_ = v_isSharedCheck_3325_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v___x_3288_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3325_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v_cache_3295_; lean_object* v_mctx_3296_; lean_object* v_zetaDeltaFVarIds_3297_; lean_object* v_postponed_3298_; lean_object* v_diag_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3324_; 
v___x_3294_ = lean_st_ref_take(v_a_3214_);
v_cache_3295_ = lean_ctor_get(v___x_3294_, 1);
v_mctx_3296_ = lean_ctor_get(v___x_3294_, 0);
v_zetaDeltaFVarIds_3297_ = lean_ctor_get(v___x_3294_, 2);
v_postponed_3298_ = lean_ctor_get(v___x_3294_, 3);
v_diag_3299_ = lean_ctor_get(v___x_3294_, 4);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3301_ = v___x_3294_;
v_isShared_3302_ = v_isSharedCheck_3324_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_diag_3299_);
lean_inc(v_postponed_3298_);
lean_inc(v_zetaDeltaFVarIds_3297_);
lean_inc(v_cache_3295_);
lean_inc(v_mctx_3296_);
lean_dec(v___x_3294_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3324_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v_inferType_3303_; lean_object* v_funInfo_3304_; lean_object* v_synthInstance_3305_; lean_object* v_whnf_3306_; lean_object* v_defEqTrans_3307_; lean_object* v_defEqPerm_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3323_; 
v_inferType_3303_ = lean_ctor_get(v_cache_3295_, 0);
v_funInfo_3304_ = lean_ctor_get(v_cache_3295_, 1);
v_synthInstance_3305_ = lean_ctor_get(v_cache_3295_, 2);
v_whnf_3306_ = lean_ctor_get(v_cache_3295_, 3);
v_defEqTrans_3307_ = lean_ctor_get(v_cache_3295_, 4);
v_defEqPerm_3308_ = lean_ctor_get(v_cache_3295_, 5);
v_isSharedCheck_3323_ = !lean_is_exclusive(v_cache_3295_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3310_ = v_cache_3295_;
v_isShared_3311_ = v_isSharedCheck_3323_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_defEqPerm_3308_);
lean_inc(v_defEqTrans_3307_);
lean_inc(v_whnf_3306_);
lean_inc(v_synthInstance_3305_);
lean_inc(v_funInfo_3304_);
lean_inc(v_inferType_3303_);
lean_dec(v_cache_3295_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3323_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3314_; 
lean_inc(v_a_3289_);
v___x_3312_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3303_, v_a_3283_, v_a_3289_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3312_);
v___x_3314_ = v___x_3310_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_funInfo_3304_);
lean_ctor_set(v_reuseFailAlloc_3322_, 2, v_synthInstance_3305_);
lean_ctor_set(v_reuseFailAlloc_3322_, 3, v_whnf_3306_);
lean_ctor_set(v_reuseFailAlloc_3322_, 4, v_defEqTrans_3307_);
lean_ctor_set(v_reuseFailAlloc_3322_, 5, v_defEqPerm_3308_);
v___x_3314_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3316_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 1, v___x_3314_);
v___x_3316_ = v___x_3301_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_mctx_3296_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_zetaDeltaFVarIds_3297_);
lean_ctor_set(v_reuseFailAlloc_3321_, 3, v_postponed_3298_);
lean_ctor_set(v_reuseFailAlloc_3321_, 4, v_diag_3299_);
v___x_3316_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3317_ = lean_st_ref_put(v_a_3214_, v___x_3316_);
if (v_isShared_3293_ == 0)
{
v___x_3319_ = v___x_3292_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3289_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3289_);
lean_dec(v_a_3283_);
return v___x_3288_;
}
}
else
{
lean_dec(v_a_3283_);
return v___x_3288_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec(v_us_3263_);
lean_dec(v_declName_3262_);
v_a_3348_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3282_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3282_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3212_, 2);
goto v___jp_3264_;
}
}
}
v___jp_3264_:
{
lean_object* v_cancelTk_x3f_3265_; 
v_cancelTk_x3f_3265_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3265_) == 1)
{
lean_object* v_val_3266_; uint8_t v___x_3267_; 
v_val_3266_ = lean_ctor_get(v_cancelTk_x3f_3265_, 0);
v___x_3267_ = l_IO_CancelToken_isSet(v_val_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3262_, v_us_3263_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v_us_3263_);
lean_dec(v_declName_3262_);
v___x_3269_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v___x_3278_; 
v___x_3278_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3262_, v_us_3263_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3278_;
}
}
}
case 5:
{
lean_object* v_fn_3356_; uint8_t v_cacheInferType_3357_; lean_object* v_nargs_3358_; lean_object* v___x_3359_; lean_object* v_dummy_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v_fn_3356_ = lean_ctor_get(v_e_3212_, 0);
v_cacheInferType_3357_ = lean_ctor_get_uint8(v_a_3213_, sizeof(void*)*7 + 3);
v_nargs_3358_ = l_Lean_Expr_getAppNumArgs(v_e_3212_);
v___x_3359_ = l_Lean_Expr_getAppFn(v_fn_3356_);
v_dummy_3360_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3358_);
v___x_3361_ = lean_mk_array(v_nargs_3358_, v_dummy_3360_);
v___x_3362_ = lean_unsigned_to_nat(1u);
v___x_3363_ = lean_nat_sub(v_nargs_3358_, v___x_3362_);
lean_dec(v_nargs_3358_);
lean_inc_ref(v_e_3212_);
v___x_3364_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3212_, v___x_3361_, v___x_3363_);
if (v_cacheInferType_3357_ == 0)
{
lean_dec_ref_known(v_e_3212_, 2);
goto v___jp_3365_;
}
else
{
uint8_t v___x_3380_; 
v___x_3380_ = l_Lean_Expr_hasMVar(v_e_3212_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3446_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3446_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3446_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3426_; lean_object* v_cache_3427_; lean_object* v_inferType_3428_; lean_object* v___x_3429_; 
v___x_3426_ = lean_st_ref_get(v_a_3214_);
v_cache_3427_ = lean_ctor_get(v___x_3426_, 1);
lean_inc_ref(v_cache_3427_);
lean_dec(v___x_3426_);
v_inferType_3428_ = lean_ctor_get(v_cache_3427_, 0);
lean_inc_ref(v_inferType_3428_);
lean_dec_ref(v_cache_3427_);
v___x_3429_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3428_, v_a_3382_);
lean_dec_ref(v_inferType_3428_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_cancelTk_x3f_3430_; 
lean_del_object(v___x_3384_);
v_cancelTk_x3f_3430_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3430_) == 1)
{
lean_object* v_val_3431_; uint8_t v___x_3432_; 
v_val_3431_ = lean_ctor_get(v_cancelTk_x3f_3430_, 0);
v___x_3432_ = l_IO_CancelToken_isSet(v_val_3431_);
if (v___x_3432_ == 0)
{
goto v___jp_3386_;
}
else
{
lean_object* v___x_3433_; lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v_a_3382_);
lean_dec_ref(v___x_3364_);
lean_dec_ref(v___x_3359_);
v___x_3433_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
goto v___jp_3386_;
}
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3444_; 
lean_dec(v_a_3382_);
lean_dec_ref(v___x_3364_);
lean_dec_ref(v___x_3359_);
v_val_3442_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_val_3442_);
lean_dec_ref_known(v___x_3429_, 1);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v_val_3442_);
v___x_3444_ = v___x_3384_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_val_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
v___jp_3386_:
{
lean_object* v___x_3387_; 
v___x_3387_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3359_, v___x_3364_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec_ref(v___x_3364_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; uint8_t v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
v___x_3389_ = l_Lean_Expr_hasMVar(v_a_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3424_; 
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v___x_3387_, 0);
lean_dec(v_unused_3425_);
v___x_3391_ = v___x_3387_;
v_isShared_3392_ = v_isSharedCheck_3424_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v___x_3387_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3424_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; lean_object* v_cache_3394_; lean_object* v_mctx_3395_; lean_object* v_zetaDeltaFVarIds_3396_; lean_object* v_postponed_3397_; lean_object* v_diag_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3423_; 
v___x_3393_ = lean_st_ref_take(v_a_3214_);
v_cache_3394_ = lean_ctor_get(v___x_3393_, 1);
v_mctx_3395_ = lean_ctor_get(v___x_3393_, 0);
v_zetaDeltaFVarIds_3396_ = lean_ctor_get(v___x_3393_, 2);
v_postponed_3397_ = lean_ctor_get(v___x_3393_, 3);
v_diag_3398_ = lean_ctor_get(v___x_3393_, 4);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3400_ = v___x_3393_;
v_isShared_3401_ = v_isSharedCheck_3423_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_diag_3398_);
lean_inc(v_postponed_3397_);
lean_inc(v_zetaDeltaFVarIds_3396_);
lean_inc(v_cache_3394_);
lean_inc(v_mctx_3395_);
lean_dec(v___x_3393_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3423_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v_inferType_3402_; lean_object* v_funInfo_3403_; lean_object* v_synthInstance_3404_; lean_object* v_whnf_3405_; lean_object* v_defEqTrans_3406_; lean_object* v_defEqPerm_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3422_; 
v_inferType_3402_ = lean_ctor_get(v_cache_3394_, 0);
v_funInfo_3403_ = lean_ctor_get(v_cache_3394_, 1);
v_synthInstance_3404_ = lean_ctor_get(v_cache_3394_, 2);
v_whnf_3405_ = lean_ctor_get(v_cache_3394_, 3);
v_defEqTrans_3406_ = lean_ctor_get(v_cache_3394_, 4);
v_defEqPerm_3407_ = lean_ctor_get(v_cache_3394_, 5);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_cache_3394_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3409_ = v_cache_3394_;
v_isShared_3410_ = v_isSharedCheck_3422_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_defEqPerm_3407_);
lean_inc(v_defEqTrans_3406_);
lean_inc(v_whnf_3405_);
lean_inc(v_synthInstance_3404_);
lean_inc(v_funInfo_3403_);
lean_inc(v_inferType_3402_);
lean_dec(v_cache_3394_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3422_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3413_; 
lean_inc(v_a_3388_);
v___x_3411_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3402_, v_a_3382_, v_a_3388_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3411_);
v___x_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_funInfo_3403_);
lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_synthInstance_3404_);
lean_ctor_set(v_reuseFailAlloc_3421_, 3, v_whnf_3405_);
lean_ctor_set(v_reuseFailAlloc_3421_, 4, v_defEqTrans_3406_);
lean_ctor_set(v_reuseFailAlloc_3421_, 5, v_defEqPerm_3407_);
v___x_3413_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3415_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 1, v___x_3413_);
v___x_3415_ = v___x_3400_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_mctx_3395_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_zetaDeltaFVarIds_3396_);
lean_ctor_set(v_reuseFailAlloc_3420_, 3, v_postponed_3397_);
lean_ctor_set(v_reuseFailAlloc_3420_, 4, v_diag_3398_);
v___x_3415_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_st_ref_put(v_a_3214_, v___x_3415_);
if (v_isShared_3392_ == 0)
{
v___x_3418_ = v___x_3391_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3388_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3388_);
lean_dec(v_a_3382_);
return v___x_3387_;
}
}
else
{
lean_dec(v_a_3382_);
return v___x_3387_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v___x_3364_);
lean_dec_ref(v___x_3359_);
v_a_3447_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3381_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3381_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3212_, 2);
goto v___jp_3365_;
}
}
v___jp_3365_:
{
lean_object* v_cancelTk_x3f_3366_; 
v_cancelTk_x3f_3366_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3366_) == 1)
{
lean_object* v_val_3367_; uint8_t v___x_3368_; 
v_val_3367_ = lean_ctor_get(v_cancelTk_x3f_3366_, 0);
v___x_3368_ = l_IO_CancelToken_isSet(v_val_3367_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; 
v___x_3369_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3359_, v___x_3364_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec_ref(v___x_3364_);
return v___x_3369_;
}
else
{
lean_object* v___x_3370_; lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v___x_3364_);
lean_dec_ref(v___x_3359_);
v___x_3370_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v___x_3379_; 
v___x_3379_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3359_, v___x_3364_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec_ref(v___x_3364_);
return v___x_3379_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3455_; 
v_cacheInferType_3455_ = lean_ctor_get_uint8(v_a_3213_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3455_ == 0)
{
goto v___jp_3233_;
}
else
{
uint8_t v___x_3456_; 
v___x_3456_ = l_Lean_Expr_hasMVar(v_e_3212_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; 
lean_inc_ref(v_e_3212_);
v___x_3457_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3522_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3522_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3522_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3502_; lean_object* v_cache_3503_; lean_object* v_inferType_3504_; lean_object* v___x_3505_; 
v___x_3502_ = lean_st_ref_get(v_a_3214_);
v_cache_3503_ = lean_ctor_get(v___x_3502_, 1);
lean_inc_ref(v_cache_3503_);
lean_dec(v___x_3502_);
v_inferType_3504_ = lean_ctor_get(v_cache_3503_, 0);
lean_inc_ref(v_inferType_3504_);
lean_dec_ref(v_cache_3503_);
v___x_3505_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3504_, v_a_3458_);
lean_dec_ref(v_inferType_3504_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_cancelTk_x3f_3506_; 
lean_del_object(v___x_3460_);
v_cancelTk_x3f_3506_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3506_) == 1)
{
lean_object* v_val_3507_; uint8_t v___x_3508_; 
v_val_3507_ = lean_ctor_get(v_cancelTk_x3f_3506_, 0);
v___x_3508_ = l_IO_CancelToken_isSet(v_val_3507_);
if (v___x_3508_ == 0)
{
goto v___jp_3462_;
}
else
{
lean_object* v___x_3509_; lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec(v_a_3458_);
lean_dec_ref_known(v_e_3212_, 3);
v___x_3509_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
goto v___jp_3462_;
}
}
else
{
lean_object* v_val_3518_; lean_object* v___x_3520_; 
lean_dec(v_a_3458_);
lean_dec_ref_known(v_e_3212_, 3);
v_val_3518_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_val_3518_);
lean_dec_ref_known(v___x_3505_, 1);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v_val_3518_);
v___x_3520_ = v___x_3460_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_val_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
v___jp_3462_:
{
lean_object* v___x_3463_; 
v___x_3463_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; uint8_t v___x_3465_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
v___x_3465_ = l_Lean_Expr_hasMVar(v_a_3464_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3500_; 
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3463_, 0);
lean_dec(v_unused_3501_);
v___x_3467_ = v___x_3463_;
v_isShared_3468_ = v_isSharedCheck_3500_;
goto v_resetjp_3466_;
}
else
{
lean_dec(v___x_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3500_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v_cache_3470_; lean_object* v_mctx_3471_; lean_object* v_zetaDeltaFVarIds_3472_; lean_object* v_postponed_3473_; lean_object* v_diag_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3499_; 
v___x_3469_ = lean_st_ref_take(v_a_3214_);
v_cache_3470_ = lean_ctor_get(v___x_3469_, 1);
v_mctx_3471_ = lean_ctor_get(v___x_3469_, 0);
v_zetaDeltaFVarIds_3472_ = lean_ctor_get(v___x_3469_, 2);
v_postponed_3473_ = lean_ctor_get(v___x_3469_, 3);
v_diag_3474_ = lean_ctor_get(v___x_3469_, 4);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3476_ = v___x_3469_;
v_isShared_3477_ = v_isSharedCheck_3499_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_diag_3474_);
lean_inc(v_postponed_3473_);
lean_inc(v_zetaDeltaFVarIds_3472_);
lean_inc(v_cache_3470_);
lean_inc(v_mctx_3471_);
lean_dec(v___x_3469_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3499_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v_inferType_3478_; lean_object* v_funInfo_3479_; lean_object* v_synthInstance_3480_; lean_object* v_whnf_3481_; lean_object* v_defEqTrans_3482_; lean_object* v_defEqPerm_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3498_; 
v_inferType_3478_ = lean_ctor_get(v_cache_3470_, 0);
v_funInfo_3479_ = lean_ctor_get(v_cache_3470_, 1);
v_synthInstance_3480_ = lean_ctor_get(v_cache_3470_, 2);
v_whnf_3481_ = lean_ctor_get(v_cache_3470_, 3);
v_defEqTrans_3482_ = lean_ctor_get(v_cache_3470_, 4);
v_defEqPerm_3483_ = lean_ctor_get(v_cache_3470_, 5);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_cache_3470_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3485_ = v_cache_3470_;
v_isShared_3486_ = v_isSharedCheck_3498_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_defEqPerm_3483_);
lean_inc(v_defEqTrans_3482_);
lean_inc(v_whnf_3481_);
lean_inc(v_synthInstance_3480_);
lean_inc(v_funInfo_3479_);
lean_inc(v_inferType_3478_);
lean_dec(v_cache_3470_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3498_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
lean_inc(v_a_3464_);
v___x_3487_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3478_, v_a_3458_, v_a_3464_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3487_);
v___x_3489_ = v___x_3485_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_funInfo_3479_);
lean_ctor_set(v_reuseFailAlloc_3497_, 2, v_synthInstance_3480_);
lean_ctor_set(v_reuseFailAlloc_3497_, 3, v_whnf_3481_);
lean_ctor_set(v_reuseFailAlloc_3497_, 4, v_defEqTrans_3482_);
lean_ctor_set(v_reuseFailAlloc_3497_, 5, v_defEqPerm_3483_);
v___x_3489_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3491_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 1, v___x_3489_);
v___x_3491_ = v___x_3476_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_mctx_3471_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_zetaDeltaFVarIds_3472_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_postponed_3473_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_diag_3474_);
v___x_3491_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3492_ = lean_st_ref_put(v_a_3214_, v___x_3491_);
if (v_isShared_3468_ == 0)
{
v___x_3494_ = v___x_3467_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3464_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
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
lean_dec(v_a_3458_);
return v___x_3463_;
}
}
else
{
lean_dec(v_a_3458_);
return v___x_3463_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref_known(v_e_3212_, 3);
v_a_3523_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3457_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3457_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
goto v___jp_3233_;
}
}
}
case 9:
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_a_3531_ = lean_ctor_get(v_e_3212_, 0);
lean_inc_ref(v_a_3531_);
lean_dec_ref_known(v_e_3212_, 1);
v___x_3532_ = l_Lean_Literal_type(v_a_3531_);
lean_dec_ref(v_a_3531_);
v___x_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
return v___x_3533_;
}
case 10:
{
lean_object* v_expr_3534_; 
v_expr_3534_ = lean_ctor_get(v_e_3212_, 1);
lean_inc_ref(v_expr_3534_);
lean_dec_ref_known(v_e_3212_, 2);
v_e_3212_ = v_expr_3534_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3536_; lean_object* v_idx_3537_; lean_object* v_struct_3538_; uint8_t v_cacheInferType_3554_; 
v_typeName_3536_ = lean_ctor_get(v_e_3212_, 0);
lean_inc(v_typeName_3536_);
v_idx_3537_ = lean_ctor_get(v_e_3212_, 1);
lean_inc(v_idx_3537_);
v_struct_3538_ = lean_ctor_get(v_e_3212_, 2);
lean_inc_ref(v_struct_3538_);
v_cacheInferType_3554_ = lean_ctor_get_uint8(v_a_3213_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3554_ == 0)
{
lean_dec_ref_known(v_e_3212_, 3);
goto v___jp_3539_;
}
else
{
uint8_t v___x_3555_; 
v___x_3555_ = l_Lean_Expr_hasMVar(v_e_3212_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3621_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3621_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3621_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3601_; lean_object* v_cache_3602_; lean_object* v_inferType_3603_; lean_object* v___x_3604_; 
v___x_3601_ = lean_st_ref_get(v_a_3214_);
v_cache_3602_ = lean_ctor_get(v___x_3601_, 1);
lean_inc_ref(v_cache_3602_);
lean_dec(v___x_3601_);
v_inferType_3603_ = lean_ctor_get(v_cache_3602_, 0);
lean_inc_ref(v_inferType_3603_);
lean_dec_ref(v_cache_3602_);
v___x_3604_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3603_, v_a_3557_);
lean_dec_ref(v_inferType_3603_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_cancelTk_x3f_3605_; 
lean_del_object(v___x_3559_);
v_cancelTk_x3f_3605_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3605_) == 1)
{
lean_object* v_val_3606_; uint8_t v___x_3607_; 
v_val_3606_ = lean_ctor_get(v_cancelTk_x3f_3605_, 0);
v___x_3607_ = l_IO_CancelToken_isSet(v_val_3606_);
if (v___x_3607_ == 0)
{
goto v___jp_3561_;
}
else
{
lean_object* v___x_3608_; lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_a_3557_);
lean_dec_ref(v_struct_3538_);
lean_dec(v_idx_3537_);
lean_dec(v_typeName_3536_);
v___x_3608_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3608_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3608_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
goto v___jp_3561_;
}
}
else
{
lean_object* v_val_3617_; lean_object* v___x_3619_; 
lean_dec(v_a_3557_);
lean_dec_ref(v_struct_3538_);
lean_dec(v_idx_3537_);
lean_dec(v_typeName_3536_);
v_val_3617_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_val_3617_);
lean_dec_ref_known(v___x_3604_, 1);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v_val_3617_);
v___x_3619_ = v___x_3559_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_val_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
v___jp_3561_:
{
lean_object* v___x_3562_; 
v___x_3562_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3536_, v_idx_3537_, v_struct_3538_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; uint8_t v___x_3564_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
v___x_3564_ = l_Lean_Expr_hasMVar(v_a_3563_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3599_; 
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3599_ == 0)
{
lean_object* v_unused_3600_; 
v_unused_3600_ = lean_ctor_get(v___x_3562_, 0);
lean_dec(v_unused_3600_);
v___x_3566_ = v___x_3562_;
v_isShared_3567_ = v_isSharedCheck_3599_;
goto v_resetjp_3565_;
}
else
{
lean_dec(v___x_3562_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3599_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v_cache_3569_; lean_object* v_mctx_3570_; lean_object* v_zetaDeltaFVarIds_3571_; lean_object* v_postponed_3572_; lean_object* v_diag_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3598_; 
v___x_3568_ = lean_st_ref_take(v_a_3214_);
v_cache_3569_ = lean_ctor_get(v___x_3568_, 1);
v_mctx_3570_ = lean_ctor_get(v___x_3568_, 0);
v_zetaDeltaFVarIds_3571_ = lean_ctor_get(v___x_3568_, 2);
v_postponed_3572_ = lean_ctor_get(v___x_3568_, 3);
v_diag_3573_ = lean_ctor_get(v___x_3568_, 4);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3575_ = v___x_3568_;
v_isShared_3576_ = v_isSharedCheck_3598_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_diag_3573_);
lean_inc(v_postponed_3572_);
lean_inc(v_zetaDeltaFVarIds_3571_);
lean_inc(v_cache_3569_);
lean_inc(v_mctx_3570_);
lean_dec(v___x_3568_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3598_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v_inferType_3577_; lean_object* v_funInfo_3578_; lean_object* v_synthInstance_3579_; lean_object* v_whnf_3580_; lean_object* v_defEqTrans_3581_; lean_object* v_defEqPerm_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3597_; 
v_inferType_3577_ = lean_ctor_get(v_cache_3569_, 0);
v_funInfo_3578_ = lean_ctor_get(v_cache_3569_, 1);
v_synthInstance_3579_ = lean_ctor_get(v_cache_3569_, 2);
v_whnf_3580_ = lean_ctor_get(v_cache_3569_, 3);
v_defEqTrans_3581_ = lean_ctor_get(v_cache_3569_, 4);
v_defEqPerm_3582_ = lean_ctor_get(v_cache_3569_, 5);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_cache_3569_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3584_ = v_cache_3569_;
v_isShared_3585_ = v_isSharedCheck_3597_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_defEqPerm_3582_);
lean_inc(v_defEqTrans_3581_);
lean_inc(v_whnf_3580_);
lean_inc(v_synthInstance_3579_);
lean_inc(v_funInfo_3578_);
lean_inc(v_inferType_3577_);
lean_dec(v_cache_3569_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3597_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
lean_inc(v_a_3563_);
v___x_3586_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3577_, v_a_3557_, v_a_3563_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3586_);
v___x_3588_ = v___x_3584_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_funInfo_3578_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_synthInstance_3579_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_whnf_3580_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_defEqTrans_3581_);
lean_ctor_set(v_reuseFailAlloc_3596_, 5, v_defEqPerm_3582_);
v___x_3588_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 1, v___x_3588_);
v___x_3590_ = v___x_3575_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_mctx_3570_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_zetaDeltaFVarIds_3571_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_postponed_3572_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v_diag_3573_);
v___x_3590_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_st_ref_put(v_a_3214_, v___x_3590_);
if (v_isShared_3567_ == 0)
{
v___x_3593_ = v___x_3566_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3563_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3563_);
lean_dec(v_a_3557_);
return v___x_3562_;
}
}
else
{
lean_dec(v_a_3557_);
return v___x_3562_;
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref(v_struct_3538_);
lean_dec(v_idx_3537_);
lean_dec(v_typeName_3536_);
v_a_3622_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3556_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3556_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
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
else
{
lean_dec_ref_known(v_e_3212_, 3);
goto v___jp_3539_;
}
}
v___jp_3539_:
{
lean_object* v_cancelTk_x3f_3540_; 
v_cancelTk_x3f_3540_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3540_) == 1)
{
lean_object* v_val_3541_; uint8_t v___x_3542_; 
v_val_3541_ = lean_ctor_get(v_cancelTk_x3f_3540_, 0);
v___x_3542_ = l_IO_CancelToken_isSet(v_val_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
v___x_3543_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3536_, v_idx_3537_, v_struct_3538_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref(v_struct_3538_);
lean_dec(v_idx_3537_);
lean_dec(v_typeName_3536_);
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
lean_object* v___x_3553_; 
v___x_3553_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3536_, v_idx_3537_, v_struct_3538_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3553_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3630_; 
v_cacheInferType_3630_ = lean_ctor_get_uint8(v_a_3213_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3630_ == 0)
{
goto v___jp_3218_;
}
else
{
uint8_t v___x_3631_; 
v___x_3631_ = l_Lean_Expr_hasMVar(v_e_3212_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; 
lean_inc_ref(v_e_3212_);
v___x_3632_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3697_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3697_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3697_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3677_; lean_object* v_cache_3678_; lean_object* v_inferType_3679_; lean_object* v___x_3680_; 
v___x_3677_ = lean_st_ref_get(v_a_3214_);
v_cache_3678_ = lean_ctor_get(v___x_3677_, 1);
lean_inc_ref(v_cache_3678_);
lean_dec(v___x_3677_);
v_inferType_3679_ = lean_ctor_get(v_cache_3678_, 0);
lean_inc_ref(v_inferType_3679_);
lean_dec_ref(v_cache_3678_);
v___x_3680_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3679_, v_a_3633_);
lean_dec_ref(v_inferType_3679_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_cancelTk_x3f_3681_; 
lean_del_object(v___x_3635_);
v_cancelTk_x3f_3681_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3681_) == 1)
{
lean_object* v_val_3682_; uint8_t v___x_3683_; 
v_val_3682_ = lean_ctor_get(v_cancelTk_x3f_3681_, 0);
v___x_3683_ = l_IO_CancelToken_isSet(v_val_3682_);
if (v___x_3683_ == 0)
{
goto v___jp_3637_;
}
else
{
lean_object* v___x_3684_; lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_a_3633_);
lean_dec_ref(v_e_3212_);
v___x_3684_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
goto v___jp_3637_;
}
}
else
{
lean_object* v_val_3693_; lean_object* v___x_3695_; 
lean_dec(v_a_3633_);
lean_dec_ref(v_e_3212_);
v_val_3693_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_val_3693_);
lean_dec_ref_known(v___x_3680_, 1);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v_val_3693_);
v___x_3695_ = v___x_3635_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_val_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
v___jp_3637_:
{
lean_object* v___x_3638_; 
v___x_3638_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; uint8_t v___x_3640_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
v___x_3640_ = l_Lean_Expr_hasMVar(v_a_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3675_; 
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v___x_3638_, 0);
lean_dec(v_unused_3676_);
v___x_3642_ = v___x_3638_;
v_isShared_3643_ = v_isSharedCheck_3675_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v___x_3638_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3675_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v_cache_3645_; lean_object* v_mctx_3646_; lean_object* v_zetaDeltaFVarIds_3647_; lean_object* v_postponed_3648_; lean_object* v_diag_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3674_; 
v___x_3644_ = lean_st_ref_take(v_a_3214_);
v_cache_3645_ = lean_ctor_get(v___x_3644_, 1);
v_mctx_3646_ = lean_ctor_get(v___x_3644_, 0);
v_zetaDeltaFVarIds_3647_ = lean_ctor_get(v___x_3644_, 2);
v_postponed_3648_ = lean_ctor_get(v___x_3644_, 3);
v_diag_3649_ = lean_ctor_get(v___x_3644_, 4);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3651_ = v___x_3644_;
v_isShared_3652_ = v_isSharedCheck_3674_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_diag_3649_);
lean_inc(v_postponed_3648_);
lean_inc(v_zetaDeltaFVarIds_3647_);
lean_inc(v_cache_3645_);
lean_inc(v_mctx_3646_);
lean_dec(v___x_3644_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3674_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_inferType_3653_; lean_object* v_funInfo_3654_; lean_object* v_synthInstance_3655_; lean_object* v_whnf_3656_; lean_object* v_defEqTrans_3657_; lean_object* v_defEqPerm_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3673_; 
v_inferType_3653_ = lean_ctor_get(v_cache_3645_, 0);
v_funInfo_3654_ = lean_ctor_get(v_cache_3645_, 1);
v_synthInstance_3655_ = lean_ctor_get(v_cache_3645_, 2);
v_whnf_3656_ = lean_ctor_get(v_cache_3645_, 3);
v_defEqTrans_3657_ = lean_ctor_get(v_cache_3645_, 4);
v_defEqPerm_3658_ = lean_ctor_get(v_cache_3645_, 5);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_cache_3645_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3660_ = v_cache_3645_;
v_isShared_3661_ = v_isSharedCheck_3673_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_defEqPerm_3658_);
lean_inc(v_defEqTrans_3657_);
lean_inc(v_whnf_3656_);
lean_inc(v_synthInstance_3655_);
lean_inc(v_funInfo_3654_);
lean_inc(v_inferType_3653_);
lean_dec(v_cache_3645_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3673_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_inc(v_a_3639_);
v___x_3662_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3653_, v_a_3633_, v_a_3639_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3662_);
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_funInfo_3654_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_synthInstance_3655_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v_whnf_3656_);
lean_ctor_set(v_reuseFailAlloc_3672_, 4, v_defEqTrans_3657_);
lean_ctor_set(v_reuseFailAlloc_3672_, 5, v_defEqPerm_3658_);
v___x_3664_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v___x_3664_);
v___x_3666_ = v___x_3651_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_mctx_3646_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_zetaDeltaFVarIds_3647_);
lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_postponed_3648_);
lean_ctor_set(v_reuseFailAlloc_3671_, 4, v_diag_3649_);
v___x_3666_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_st_ref_put(v_a_3214_, v___x_3666_);
if (v_isShared_3643_ == 0)
{
v___x_3669_ = v___x_3642_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3639_);
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
}
}
}
else
{
lean_dec(v_a_3639_);
lean_dec(v_a_3633_);
return v___x_3638_;
}
}
else
{
lean_dec(v_a_3633_);
return v___x_3638_;
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v_e_3212_);
v_a_3698_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3632_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3632_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
goto v___jp_3218_;
}
}
}
}
v___jp_3218_:
{
lean_object* v_cancelTk_x3f_3219_; 
v_cancelTk_x3f_3219_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3219_) == 1)
{
lean_object* v_val_3220_; uint8_t v___x_3221_; 
v_val_3220_ = lean_ctor_get(v_cancelTk_x3f_3219_, 0);
v___x_3221_ = l_IO_CancelToken_isSet(v_val_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v_e_3212_);
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
v___x_3232_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3232_;
}
}
v___jp_3233_:
{
lean_object* v_cancelTk_x3f_3234_; 
v_cancelTk_x3f_3234_ = lean_ctor_get(v_a_3215_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3234_) == 1)
{
lean_object* v_val_3235_; uint8_t v___x_3236_; 
v_val_3235_ = lean_ctor_get(v_cancelTk_x3f_3234_, 0);
v___x_3236_ = l_IO_CancelToken_isSet(v_val_3235_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; 
v___x_3237_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec_ref(v_e_3212_);
v___x_3238_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
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
else
{
lean_object* v___x_3247_; 
v___x_3247_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
return v___x_3247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3713_, lean_object* v_x_3714_, lean_object* v_x_3715_, lean_object* v_x_3716_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3714_, v_x_3715_, v_x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3718_, lean_object* v_x_3719_, lean_object* v_x_3720_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3719_, v_x_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3722_, lean_object* v_x_3723_, lean_object* v_x_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3722_, v_x_3723_, v_x_3724_);
lean_dec_ref(v_x_3724_);
lean_dec_ref(v_x_3723_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3726_, lean_object* v_x_3727_, size_t v_x_3728_, size_t v_x_3729_, lean_object* v_x_3730_, lean_object* v_x_3731_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3727_, v_x_3728_, v_x_3729_, v_x_3730_, v_x_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3733_, lean_object* v_x_3734_, lean_object* v_x_3735_, lean_object* v_x_3736_, lean_object* v_x_3737_, lean_object* v_x_3738_){
_start:
{
size_t v_x_4009__boxed_3739_; size_t v_x_4010__boxed_3740_; lean_object* v_res_3741_; 
v_x_4009__boxed_3739_ = lean_unbox_usize(v_x_3735_);
lean_dec(v_x_3735_);
v_x_4010__boxed_3740_ = lean_unbox_usize(v_x_3736_);
lean_dec(v_x_3736_);
v_res_3741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3733_, v_x_3734_, v_x_4009__boxed_3739_, v_x_4010__boxed_3740_, v_x_3737_, v_x_3738_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3742_, lean_object* v_x_3743_, size_t v_x_3744_, lean_object* v_x_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3743_, v_x_3744_, v_x_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3747_, lean_object* v_x_3748_, lean_object* v_x_3749_, lean_object* v_x_3750_){
_start:
{
size_t v_x_4026__boxed_3751_; lean_object* v_res_3752_; 
v_x_4026__boxed_3751_ = lean_unbox_usize(v_x_3749_);
lean_dec(v_x_3749_);
v_res_3752_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3747_, v_x_3748_, v_x_4026__boxed_3751_, v_x_3750_);
lean_dec_ref(v_x_3750_);
lean_dec_ref(v_x_3748_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3753_, lean_object* v_n_3754_, lean_object* v_k_3755_, lean_object* v_v_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3754_, v_k_3755_, v_v_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3758_, size_t v_depth_3759_, lean_object* v_keys_3760_, lean_object* v_vals_3761_, lean_object* v_heq_3762_, lean_object* v_i_3763_, lean_object* v_entries_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3759_, v_keys_3760_, v_vals_3761_, v_i_3763_, v_entries_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3766_, lean_object* v_depth_3767_, lean_object* v_keys_3768_, lean_object* v_vals_3769_, lean_object* v_heq_3770_, lean_object* v_i_3771_, lean_object* v_entries_3772_){
_start:
{
size_t v_depth_boxed_3773_; lean_object* v_res_3774_; 
v_depth_boxed_3773_ = lean_unbox_usize(v_depth_3767_);
lean_dec(v_depth_3767_);
v_res_3774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3766_, v_depth_boxed_3773_, v_keys_3768_, v_vals_3769_, v_heq_3770_, v_i_3771_, v_entries_3772_);
lean_dec_ref(v_vals_3769_);
lean_dec_ref(v_keys_3768_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3775_, lean_object* v_keys_3776_, lean_object* v_vals_3777_, lean_object* v_heq_3778_, lean_object* v_i_3779_, lean_object* v_k_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3776_, v_vals_3777_, v_i_3779_, v_k_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3782_, lean_object* v_keys_3783_, lean_object* v_vals_3784_, lean_object* v_heq_3785_, lean_object* v_i_3786_, lean_object* v_k_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3782_, v_keys_3783_, v_vals_3784_, v_heq_3785_, v_i_3786_, v_k_3787_);
lean_dec_ref(v_k_3787_);
lean_dec_ref(v_vals_3784_);
lean_dec_ref(v_keys_3783_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3789_, lean_object* v_x_3790_, lean_object* v_x_3791_, lean_object* v_x_3792_, lean_object* v_x_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3790_, v_x_3791_, v_x_3792_, v_x_3793_);
return v___x_3794_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = l_Lean_maxRecDepthErrorMessage;
v___x_3801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
return v___x_3801_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3803_ = l_Lean_MessageData_ofFormat(v___x_3802_);
return v___x_3803_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3805_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3806_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___x_3804_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3807_){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3809_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3810_, 0, v_ref_3807_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3812_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3815_, lean_object* v_ref_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3816_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3823_, lean_object* v_ref_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3823_, v_ref_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v___y_3838_; lean_object* v___y_3839_; uint8_t v___y_3840_; lean_object* v___y_3841_; uint8_t v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; uint8_t v___y_3848_; uint8_t v___y_3849_; lean_object* v___y_3879_; uint8_t v___y_3880_; lean_object* v_fileName_3913_; lean_object* v_fileMap_3914_; lean_object* v_options_3915_; lean_object* v_currRecDepth_3916_; lean_object* v_maxRecDepth_3917_; lean_object* v_ref_3918_; lean_object* v_currNamespace_3919_; lean_object* v_openDecls_3920_; lean_object* v_initHeartbeats_3921_; lean_object* v_maxHeartbeats_3922_; lean_object* v_quotContext_3923_; lean_object* v_currMacroScope_3924_; uint8_t v_diag_3925_; lean_object* v_cancelTk_x3f_3926_; uint8_t v_suppressElabErrors_3927_; lean_object* v_inheritedTraceOptions_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3946_; 
v_fileName_3913_ = lean_ctor_get(v_a_3834_, 0);
v_fileMap_3914_ = lean_ctor_get(v_a_3834_, 1);
v_options_3915_ = lean_ctor_get(v_a_3834_, 2);
v_currRecDepth_3916_ = lean_ctor_get(v_a_3834_, 3);
v_maxRecDepth_3917_ = lean_ctor_get(v_a_3834_, 4);
v_ref_3918_ = lean_ctor_get(v_a_3834_, 5);
v_currNamespace_3919_ = lean_ctor_get(v_a_3834_, 6);
v_openDecls_3920_ = lean_ctor_get(v_a_3834_, 7);
v_initHeartbeats_3921_ = lean_ctor_get(v_a_3834_, 8);
v_maxHeartbeats_3922_ = lean_ctor_get(v_a_3834_, 9);
v_quotContext_3923_ = lean_ctor_get(v_a_3834_, 10);
v_currMacroScope_3924_ = lean_ctor_get(v_a_3834_, 11);
v_diag_3925_ = lean_ctor_get_uint8(v_a_3834_, sizeof(void*)*14);
v_cancelTk_x3f_3926_ = lean_ctor_get(v_a_3834_, 12);
v_suppressElabErrors_3927_ = lean_ctor_get_uint8(v_a_3834_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3928_ = lean_ctor_get(v_a_3834_, 13);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_a_3834_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3930_ = v_a_3834_;
v_isShared_3931_ = v_isSharedCheck_3946_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_inheritedTraceOptions_3928_);
lean_inc(v_cancelTk_x3f_3926_);
lean_inc(v_currMacroScope_3924_);
lean_inc(v_quotContext_3923_);
lean_inc(v_maxHeartbeats_3922_);
lean_inc(v_initHeartbeats_3921_);
lean_inc(v_openDecls_3920_);
lean_inc(v_currNamespace_3919_);
lean_inc(v_ref_3918_);
lean_inc(v_maxRecDepth_3917_);
lean_inc(v_currRecDepth_3916_);
lean_inc(v_options_3915_);
lean_inc(v_fileMap_3914_);
lean_inc(v_fileName_3913_);
lean_dec(v_a_3834_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3946_;
goto v_resetjp_3929_;
}
v___jp_3837_:
{
lean_object* v___x_3850_; uint8_t v_foApprox_3851_; uint8_t v_ctxApprox_3852_; uint8_t v_quasiPatternApprox_3853_; uint8_t v_constApprox_3854_; uint8_t v_isDefEqStuckEx_3855_; uint8_t v_unificationHints_3856_; uint8_t v_proofIrrelevance_3857_; uint8_t v_assignSyntheticOpaque_3858_; uint8_t v_offsetCnstrs_3859_; uint8_t v_transparency_3860_; uint8_t v_univApprox_3861_; uint8_t v_zetaUnused_3862_; uint8_t v_canUnfoldPredicateConfig_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3877_; 
v___x_3850_ = l_Lean_Meta_Context_config(v___y_3845_);
lean_dec_ref(v___y_3845_);
v_foApprox_3851_ = lean_ctor_get_uint8(v___x_3850_, 0);
v_ctxApprox_3852_ = lean_ctor_get_uint8(v___x_3850_, 1);
v_quasiPatternApprox_3853_ = lean_ctor_get_uint8(v___x_3850_, 2);
v_constApprox_3854_ = lean_ctor_get_uint8(v___x_3850_, 3);
v_isDefEqStuckEx_3855_ = lean_ctor_get_uint8(v___x_3850_, 4);
v_unificationHints_3856_ = lean_ctor_get_uint8(v___x_3850_, 5);
v_proofIrrelevance_3857_ = lean_ctor_get_uint8(v___x_3850_, 6);
v_assignSyntheticOpaque_3858_ = lean_ctor_get_uint8(v___x_3850_, 7);
v_offsetCnstrs_3859_ = lean_ctor_get_uint8(v___x_3850_, 8);
v_transparency_3860_ = lean_ctor_get_uint8(v___x_3850_, 9);
v_univApprox_3861_ = lean_ctor_get_uint8(v___x_3850_, 11);
v_zetaUnused_3862_ = lean_ctor_get_uint8(v___x_3850_, 17);
v_canUnfoldPredicateConfig_3863_ = lean_ctor_get_uint8(v___x_3850_, 19);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3865_ = v___x_3850_;
v_isShared_3866_ = v_isSharedCheck_3877_;
goto v_resetjp_3864_;
}
else
{
lean_dec(v___x_3850_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3877_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
uint8_t v___x_3867_; uint8_t v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3871_; 
v___x_3867_ = 1;
v___x_3868_ = 0;
v___x_3869_ = 2;
if (v_isShared_3866_ == 0)
{
v___x_3871_ = v___x_3865_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 0, v_foApprox_3851_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 1, v_ctxApprox_3852_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 2, v_quasiPatternApprox_3853_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 3, v_constApprox_3854_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 4, v_isDefEqStuckEx_3855_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 5, v_unificationHints_3856_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 6, v_proofIrrelevance_3857_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 7, v_assignSyntheticOpaque_3858_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 8, v_offsetCnstrs_3859_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 9, v_transparency_3860_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 11, v_univApprox_3861_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 17, v_zetaUnused_3862_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, 19, v_canUnfoldPredicateConfig_3863_);
v___x_3871_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
uint64_t v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_ctor_set_uint8(v___x_3871_, 10, v___x_3868_);
lean_ctor_set_uint8(v___x_3871_, 12, v___x_3867_);
lean_ctor_set_uint8(v___x_3871_, 13, v___x_3867_);
lean_ctor_set_uint8(v___x_3871_, 14, v___x_3869_);
lean_ctor_set_uint8(v___x_3871_, 15, v___x_3867_);
lean_ctor_set_uint8(v___x_3871_, 16, v___x_3867_);
lean_ctor_set_uint8(v___x_3871_, 18, v___x_3867_);
v___x_3872_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3871_);
v___x_3873_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
lean_ctor_set_uint64(v___x_3873_, sizeof(void*)*1, v___x_3872_);
v___x_3874_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v___y_3846_);
lean_ctor_set(v___x_3874_, 2, v___y_3838_);
lean_ctor_set(v___x_3874_, 3, v___y_3843_);
lean_ctor_set(v___x_3874_, 4, v___y_3839_);
lean_ctor_set(v___x_3874_, 5, v___y_3841_);
lean_ctor_set(v___x_3874_, 6, v___y_3847_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7, v___y_3848_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7 + 1, v___y_3849_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7 + 2, v___y_3842_);
lean_ctor_set_uint8(v___x_3874_, sizeof(void*)*7 + 3, v___y_3840_);
v___x_3875_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3831_, v___x_3874_, v_a_3833_, v___y_3844_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v___y_3844_);
lean_dec(v_a_3833_);
lean_dec_ref_known(v___x_3874_, 7);
return v___x_3875_;
}
}
}
v___jp_3878_:
{
lean_object* v_keyedConfig_3881_; uint8_t v_trackZetaDelta_3882_; lean_object* v_zetaDeltaSet_3883_; lean_object* v_lctx_3884_; lean_object* v_localInstances_3885_; lean_object* v_defEqCtx_x3f_3886_; lean_object* v_synthPendingDepth_3887_; lean_object* v_customCanUnfoldPredicate_x3f_3888_; uint8_t v_univApprox_3889_; uint8_t v_inTypeClassResolution_3890_; uint8_t v_cacheInferType_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3912_; 
v_keyedConfig_3881_ = lean_ctor_get(v_a_3832_, 0);
v_trackZetaDelta_3882_ = lean_ctor_get_uint8(v_a_3832_, sizeof(void*)*7);
v_zetaDeltaSet_3883_ = lean_ctor_get(v_a_3832_, 1);
v_lctx_3884_ = lean_ctor_get(v_a_3832_, 2);
v_localInstances_3885_ = lean_ctor_get(v_a_3832_, 3);
v_defEqCtx_x3f_3886_ = lean_ctor_get(v_a_3832_, 4);
v_synthPendingDepth_3887_ = lean_ctor_get(v_a_3832_, 5);
v_customCanUnfoldPredicate_x3f_3888_ = lean_ctor_get(v_a_3832_, 6);
v_univApprox_3889_ = lean_ctor_get_uint8(v_a_3832_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3890_ = lean_ctor_get_uint8(v_a_3832_, sizeof(void*)*7 + 2);
v_cacheInferType_3891_ = lean_ctor_get_uint8(v_a_3832_, sizeof(void*)*7 + 3);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_a_3832_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3893_ = v_a_3832_;
v_isShared_3894_ = v_isSharedCheck_3912_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3888_);
lean_inc(v_synthPendingDepth_3887_);
lean_inc(v_defEqCtx_x3f_3886_);
lean_inc(v_localInstances_3885_);
lean_inc(v_lctx_3884_);
lean_inc(v_zetaDeltaSet_3883_);
lean_inc(v_keyedConfig_3881_);
lean_dec(v_a_3832_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3912_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3895_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_3880_, v_keyedConfig_3881_);
lean_inc(v_customCanUnfoldPredicate_x3f_3888_);
lean_inc(v_synthPendingDepth_3887_);
lean_inc(v_defEqCtx_x3f_3886_);
lean_inc_ref(v_localInstances_3885_);
lean_inc_ref(v_lctx_3884_);
lean_inc(v_zetaDeltaSet_3883_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3895_);
v___x_3897_ = v___x_3893_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_zetaDeltaSet_3883_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_lctx_3884_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_localInstances_3885_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_defEqCtx_x3f_3886_);
lean_ctor_set(v_reuseFailAlloc_3911_, 5, v_synthPendingDepth_3887_);
lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_customCanUnfoldPredicate_x3f_3888_);
lean_ctor_set_uint8(v_reuseFailAlloc_3911_, sizeof(void*)*7, v_trackZetaDelta_3882_);
lean_ctor_set_uint8(v_reuseFailAlloc_3911_, sizeof(void*)*7 + 1, v_univApprox_3889_);
lean_ctor_set_uint8(v_reuseFailAlloc_3911_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3890_);
lean_ctor_set_uint8(v_reuseFailAlloc_3911_, sizeof(void*)*7 + 3, v_cacheInferType_3891_);
v___x_3897_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; uint8_t v_beta_3899_; 
v___x_3898_ = l_Lean_Meta_Context_config(v___x_3897_);
v_beta_3899_ = lean_ctor_get_uint8(v___x_3898_, 13);
if (v_beta_3899_ == 0)
{
lean_dec_ref(v___x_3898_);
v___y_3838_ = v_lctx_3884_;
v___y_3839_ = v_defEqCtx_x3f_3886_;
v___y_3840_ = v_cacheInferType_3891_;
v___y_3841_ = v_synthPendingDepth_3887_;
v___y_3842_ = v_inTypeClassResolution_3890_;
v___y_3843_ = v_localInstances_3885_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___x_3897_;
v___y_3846_ = v_zetaDeltaSet_3883_;
v___y_3847_ = v_customCanUnfoldPredicate_x3f_3888_;
v___y_3848_ = v_trackZetaDelta_3882_;
v___y_3849_ = v_univApprox_3889_;
goto v___jp_3837_;
}
else
{
uint8_t v_iota_3900_; 
v_iota_3900_ = lean_ctor_get_uint8(v___x_3898_, 12);
if (v_iota_3900_ == 0)
{
lean_dec_ref(v___x_3898_);
v___y_3838_ = v_lctx_3884_;
v___y_3839_ = v_defEqCtx_x3f_3886_;
v___y_3840_ = v_cacheInferType_3891_;
v___y_3841_ = v_synthPendingDepth_3887_;
v___y_3842_ = v_inTypeClassResolution_3890_;
v___y_3843_ = v_localInstances_3885_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___x_3897_;
v___y_3846_ = v_zetaDeltaSet_3883_;
v___y_3847_ = v_customCanUnfoldPredicate_x3f_3888_;
v___y_3848_ = v_trackZetaDelta_3882_;
v___y_3849_ = v_univApprox_3889_;
goto v___jp_3837_;
}
else
{
uint8_t v_zeta_3901_; 
v_zeta_3901_ = lean_ctor_get_uint8(v___x_3898_, 15);
if (v_zeta_3901_ == 0)
{
lean_dec_ref(v___x_3898_);
v___y_3838_ = v_lctx_3884_;
v___y_3839_ = v_defEqCtx_x3f_3886_;
v___y_3840_ = v_cacheInferType_3891_;
v___y_3841_ = v_synthPendingDepth_3887_;
v___y_3842_ = v_inTypeClassResolution_3890_;
v___y_3843_ = v_localInstances_3885_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___x_3897_;
v___y_3846_ = v_zetaDeltaSet_3883_;
v___y_3847_ = v_customCanUnfoldPredicate_x3f_3888_;
v___y_3848_ = v_trackZetaDelta_3882_;
v___y_3849_ = v_univApprox_3889_;
goto v___jp_3837_;
}
else
{
uint8_t v_zetaHave_3902_; 
v_zetaHave_3902_ = lean_ctor_get_uint8(v___x_3898_, 18);
if (v_zetaHave_3902_ == 0)
{
lean_dec_ref(v___x_3898_);
v___y_3838_ = v_lctx_3884_;
v___y_3839_ = v_defEqCtx_x3f_3886_;
v___y_3840_ = v_cacheInferType_3891_;
v___y_3841_ = v_synthPendingDepth_3887_;
v___y_3842_ = v_inTypeClassResolution_3890_;
v___y_3843_ = v_localInstances_3885_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___x_3897_;
v___y_3846_ = v_zetaDeltaSet_3883_;
v___y_3847_ = v_customCanUnfoldPredicate_x3f_3888_;
v___y_3848_ = v_trackZetaDelta_3882_;
v___y_3849_ = v_univApprox_3889_;
goto v___jp_3837_;
}
else
{
uint8_t v_zetaDelta_3903_; 
v_zetaDelta_3903_ = lean_ctor_get_uint8(v___x_3898_, 16);
if (v_zetaDelta_3903_ == 0)
{
lean_dec_ref(v___x_3898_);
v___y_3838_ = v_lctx_3884_;
v___y_3839_ = v_defEqCtx_x3f_3886_;
v___y_3840_ = v_cacheInferType_3891_;
v___y_3841_ = v_synthPendingDepth_3887_;
v___y_3842_ = v_inTypeClassResolution_3890_;
v___y_3843_ = v_localInstances_3885_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___x_3897_;
v___y_3846_ = v_zetaDeltaSet_3883_;
v___y_3847_ = v_customCanUnfoldPredicate_x3f_3888_;
v___y_3848_ = v_trackZetaDelta_3882_;
v___y_3849_ = v_univApprox_3889_;
goto v___jp_3837_;
}
else
{
uint8_t v_etaStruct_3904_; uint8_t v_proj_3905_; uint8_t v___x_3906_; uint8_t v___x_3907_; 
v_etaStruct_3904_ = lean_ctor_get_uint8(v___x_3898_, 10);
v_proj_3905_ = lean_ctor_get_uint8(v___x_3898_, 14);
lean_dec_ref(v___x_3898_);
v___x_3906_ = 2;
v___x_3907_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3905_, v___x_3906_);
if (v___x_3907_ == 0)
{
v___y_3838_ = v_lctx_3884_;
v___y_3839_ = v_defEqCtx_x3f_3886_;
v___y_3840_ = v_cacheInferType_3891_;
v___y_3841_ = v_synthPendingDepth_3887_;
v___y_3842_ = v_inTypeClassResolution_3890_;
v___y_3843_ = v_localInstances_3885_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___x_3897_;
v___y_3846_ = v_zetaDeltaSet_3883_;
v___y_3847_ = v_customCanUnfoldPredicate_x3f_3888_;
v___y_3848_ = v_trackZetaDelta_3882_;
v___y_3849_ = v_univApprox_3889_;
goto v___jp_3837_;
}
else
{
uint8_t v___x_3908_; uint8_t v___x_3909_; 
v___x_3908_ = 0;
v___x_3909_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3904_, v___x_3908_);
if (v___x_3909_ == 0)
{
v___y_3838_ = v_lctx_3884_;
v___y_3839_ = v_defEqCtx_x3f_3886_;
v___y_3840_ = v_cacheInferType_3891_;
v___y_3841_ = v_synthPendingDepth_3887_;
v___y_3842_ = v_inTypeClassResolution_3890_;
v___y_3843_ = v_localInstances_3885_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___x_3897_;
v___y_3846_ = v_zetaDeltaSet_3883_;
v___y_3847_ = v_customCanUnfoldPredicate_x3f_3888_;
v___y_3848_ = v_trackZetaDelta_3882_;
v___y_3849_ = v_univApprox_3889_;
goto v___jp_3837_;
}
else
{
lean_object* v___x_3910_; 
lean_dec(v_customCanUnfoldPredicate_x3f_3888_);
lean_dec(v_synthPendingDepth_3887_);
lean_dec(v_defEqCtx_x3f_3886_);
lean_dec_ref(v_localInstances_3885_);
lean_dec_ref(v_lctx_3884_);
lean_dec(v_zetaDeltaSet_3883_);
v___x_3910_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3831_, v___x_3897_, v_a_3833_, v___y_3879_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v___y_3879_);
lean_dec(v_a_3833_);
lean_dec_ref(v___x_3897_);
return v___x_3910_;
}
}
}
}
}
}
}
}
}
}
v_resetjp_3929_:
{
lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3942_ = lean_unsigned_to_nat(0u);
v___x_3943_ = lean_nat_dec_eq(v_maxRecDepth_3917_, v___x_3942_);
if (v___x_3943_ == 0)
{
uint8_t v___x_3944_; 
v___x_3944_ = lean_nat_dec_eq(v_currRecDepth_3916_, v_maxRecDepth_3917_);
if (v___x_3944_ == 0)
{
goto v___jp_3932_;
}
else
{
lean_object* v___x_3945_; 
lean_del_object(v___x_3930_);
lean_dec_ref(v_inheritedTraceOptions_3928_);
lean_dec(v_cancelTk_x3f_3926_);
lean_dec(v_currMacroScope_3924_);
lean_dec(v_quotContext_3923_);
lean_dec(v_maxHeartbeats_3922_);
lean_dec(v_initHeartbeats_3921_);
lean_dec(v_openDecls_3920_);
lean_dec(v_currNamespace_3919_);
lean_dec(v_maxRecDepth_3917_);
lean_dec(v_currRecDepth_3916_);
lean_dec_ref(v_options_3915_);
lean_dec_ref(v_fileMap_3914_);
lean_dec_ref(v_fileName_3913_);
lean_dec(v_a_3835_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec_ref(v_e_3831_);
v___x_3945_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3918_);
return v___x_3945_;
}
}
else
{
goto v___jp_3932_;
}
v___jp_3932_:
{
lean_object* v___x_3933_; uint8_t v_transparency_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3933_ = l_Lean_Meta_Context_config(v_a_3832_);
v_transparency_3934_ = lean_ctor_get_uint8(v___x_3933_, 9);
lean_dec_ref(v___x_3933_);
v___x_3935_ = lean_unsigned_to_nat(1u);
v___x_3936_ = lean_nat_add(v_currRecDepth_3916_, v___x_3935_);
lean_dec(v_currRecDepth_3916_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 3, v___x_3936_);
v___x_3938_ = v___x_3930_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_fileName_3913_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_fileMap_3914_);
lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_options_3915_);
lean_ctor_set(v_reuseFailAlloc_3941_, 3, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_maxRecDepth_3917_);
lean_ctor_set(v_reuseFailAlloc_3941_, 5, v_ref_3918_);
lean_ctor_set(v_reuseFailAlloc_3941_, 6, v_currNamespace_3919_);
lean_ctor_set(v_reuseFailAlloc_3941_, 7, v_openDecls_3920_);
lean_ctor_set(v_reuseFailAlloc_3941_, 8, v_initHeartbeats_3921_);
lean_ctor_set(v_reuseFailAlloc_3941_, 9, v_maxHeartbeats_3922_);
lean_ctor_set(v_reuseFailAlloc_3941_, 10, v_quotContext_3923_);
lean_ctor_set(v_reuseFailAlloc_3941_, 11, v_currMacroScope_3924_);
lean_ctor_set(v_reuseFailAlloc_3941_, 12, v_cancelTk_x3f_3926_);
lean_ctor_set(v_reuseFailAlloc_3941_, 13, v_inheritedTraceOptions_3928_);
lean_ctor_set_uint8(v_reuseFailAlloc_3941_, sizeof(void*)*14, v_diag_3925_);
lean_ctor_set_uint8(v_reuseFailAlloc_3941_, sizeof(void*)*14 + 1, v_suppressElabErrors_3927_);
v___x_3938_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
uint8_t v___x_3939_; uint8_t v___x_3940_; 
v___x_3939_ = 1;
v___x_3940_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3934_, v___x_3939_);
if (v___x_3940_ == 0)
{
v___y_3879_ = v___x_3938_;
v___y_3880_ = v_transparency_3934_;
goto v___jp_3878_;
}
else
{
v___y_3879_ = v___x_3938_;
v___y_3880_ = v___x_3939_;
goto v___jp_3878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = lean_infer_type(v_e_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v_res_3953_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3954_){
_start:
{
switch(lean_obj_tag(v_x_3954_))
{
case 0:
{
uint8_t v___x_3955_; 
v___x_3955_ = 1;
return v___x_3955_;
}
case 2:
{
lean_object* v_a_3956_; lean_object* v_a_3957_; uint8_t v___x_3958_; 
v_a_3956_ = lean_ctor_get(v_x_3954_, 0);
v_a_3957_ = lean_ctor_get(v_x_3954_, 1);
v___x_3958_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3956_);
if (v___x_3958_ == 0)
{
return v___x_3958_;
}
else
{
v_x_3954_ = v_a_3957_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3960_; 
v_a_3960_ = lean_ctor_get(v_x_3954_, 1);
v_x_3954_ = v_a_3960_;
goto _start;
}
default: 
{
uint8_t v___x_3962_; 
v___x_3962_ = 0;
return v___x_3962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3963_){
_start:
{
uint8_t v_res_3964_; lean_object* v_r_3965_; 
v_res_3964_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3963_);
lean_dec(v_x_3963_);
v_r_3965_ = lean_box(v_res_3964_);
return v_r_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; lean_object* v_mctx_3970_; lean_object* v___x_3971_; lean_object* v_fst_3972_; lean_object* v_snd_3973_; lean_object* v___x_3974_; lean_object* v_cache_3975_; lean_object* v_zetaDeltaFVarIds_3976_; lean_object* v_postponed_3977_; lean_object* v_diag_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3987_; 
v___x_3969_ = lean_st_ref_get(v___y_3967_);
v_mctx_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc_ref(v_mctx_3970_);
lean_dec(v___x_3969_);
v___x_3971_ = lean_instantiate_level_mvars(v_mctx_3970_, v_l_3966_);
v_fst_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_fst_3972_);
v_snd_3973_ = lean_ctor_get(v___x_3971_, 1);
lean_inc(v_snd_3973_);
lean_dec_ref(v___x_3971_);
v___x_3974_ = lean_st_ref_take(v___y_3967_);
v_cache_3975_ = lean_ctor_get(v___x_3974_, 1);
v_zetaDeltaFVarIds_3976_ = lean_ctor_get(v___x_3974_, 2);
v_postponed_3977_ = lean_ctor_get(v___x_3974_, 3);
v_diag_3978_ = lean_ctor_get(v___x_3974_, 4);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v___x_3974_, 0);
lean_dec(v_unused_3988_);
v___x_3980_ = v___x_3974_;
v_isShared_3981_ = v_isSharedCheck_3987_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_diag_3978_);
lean_inc(v_postponed_3977_);
lean_inc(v_zetaDeltaFVarIds_3976_);
lean_inc(v_cache_3975_);
lean_dec(v___x_3974_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3987_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v_fst_3972_);
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_fst_3972_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_cache_3975_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_zetaDeltaFVarIds_3976_);
lean_ctor_set(v_reuseFailAlloc_3986_, 3, v_postponed_3977_);
lean_ctor_set(v_reuseFailAlloc_3986_, 4, v_diag_3978_);
v___x_3983_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = lean_st_ref_put(v___y_3967_, v___x_3983_);
v___x_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3985_, 0, v_snd_3973_);
return v___x_3985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3989_, v___y_3990_);
lean_dec(v___y_3990_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3993_, v___y_3995_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_4007_, lean_object* v_x_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
switch(lean_obj_tag(v_x_4007_))
{
case 3:
{
lean_object* v_u_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; 
v_u_4018_ = lean_ctor_get(v_x_4007_, 0);
lean_inc(v_u_4018_);
lean_dec_ref_known(v_x_4007_, 1);
v___x_4019_ = lean_unsigned_to_nat(0u);
v___x_4020_ = lean_nat_dec_eq(v_x_4008_, v___x_4019_);
lean_dec(v_x_4008_);
if (v___x_4020_ == 0)
{
lean_dec(v_u_4018_);
goto v___jp_4014_;
}
else
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4018_, v_a_4010_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4032_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4032_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4032_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
uint8_t v___x_4026_; uint8_t v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4026_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4022_);
lean_dec(v_a_4022_);
v___x_4027_ = l_Lean_Bool_toLBool(v___x_4026_);
v___x_4028_ = lean_box(v___x_4027_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4028_);
v___x_4030_ = v___x_4024_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
v_a_4033_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4021_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4021_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
case 7:
{
lean_object* v_body_4041_; lean_object* v_zero_4042_; uint8_t v_isZero_4043_; 
v_body_4041_ = lean_ctor_get(v_x_4007_, 2);
lean_inc_ref(v_body_4041_);
lean_dec_ref_known(v_x_4007_, 3);
v_zero_4042_ = lean_unsigned_to_nat(0u);
v_isZero_4043_ = lean_nat_dec_eq(v_x_4008_, v_zero_4042_);
if (v_isZero_4043_ == 1)
{
uint8_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_dec_ref(v_body_4041_);
lean_dec(v_x_4008_);
v___x_4044_ = 0;
v___x_4045_ = lean_box(v___x_4044_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
else
{
lean_object* v_one_4047_; lean_object* v_n_4048_; 
v_one_4047_ = lean_unsigned_to_nat(1u);
v_n_4048_ = lean_nat_sub(v_x_4008_, v_one_4047_);
lean_dec(v_x_4008_);
v_x_4007_ = v_body_4041_;
v_x_4008_ = v_n_4048_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4050_; 
v_body_4050_ = lean_ctor_get(v_x_4007_, 3);
lean_inc_ref(v_body_4050_);
lean_dec_ref_known(v_x_4007_, 4);
v_x_4007_ = v_body_4050_;
goto _start;
}
case 10:
{
lean_object* v_expr_4052_; 
v_expr_4052_ = lean_ctor_get(v_x_4007_, 1);
lean_inc_ref(v_expr_4052_);
lean_dec_ref_known(v_x_4007_, 2);
v_x_4007_ = v_expr_4052_;
goto _start;
}
default: 
{
lean_dec(v_x_4008_);
lean_dec_ref(v_x_4007_);
goto v___jp_4014_;
}
}
v___jp_4014_:
{
uint8_t v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = 2;
v___x_4016_ = lean_box(v___x_4015_);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_4054_, lean_object* v_x_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_4054_, v_x_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_4062_, lean_object* v_x_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
switch(lean_obj_tag(v_x_4062_))
{
case 4:
{
lean_object* v_declName_4069_; lean_object* v_us_4070_; lean_object* v___x_4071_; 
v_declName_4069_ = lean_ctor_get(v_x_4062_, 0);
lean_inc(v_declName_4069_);
v_us_4070_ = lean_ctor_get(v_x_4062_, 1);
lean_inc(v_us_4070_);
lean_dec_ref_known(v_x_4062_, 2);
v___x_4071_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4069_, v_us_4070_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4072_, v_x_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
return v___x_4073_;
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v_x_4063_);
v_a_4074_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4071_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4071_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4082_; lean_object* v___x_4083_; 
v_fvarId_4082_ = lean_ctor_get(v_x_4062_, 0);
lean_inc(v_fvarId_4082_);
lean_dec_ref_known(v_x_4062_, 1);
v___x_4083_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4082_, v_a_4064_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v___x_4085_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4084_, v_x_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
return v___x_4085_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_x_4063_);
v_a_4086_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4083_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4083_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4094_; lean_object* v___x_4095_; 
v_mvarId_4094_ = lean_ctor_get(v_x_4062_, 0);
lean_inc(v_mvarId_4094_);
lean_dec_ref_known(v_x_4062_, 1);
v___x_4095_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4094_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4097_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v___x_4097_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4096_, v_x_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
return v___x_4097_;
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_x_4063_);
v_a_4098_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4095_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4095_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
case 5:
{
lean_object* v_fn_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v_fn_4106_ = lean_ctor_get(v_x_4062_, 0);
lean_inc_ref(v_fn_4106_);
lean_dec_ref_known(v_x_4062_, 2);
v___x_4107_ = lean_unsigned_to_nat(1u);
v___x_4108_ = lean_nat_add(v_x_4063_, v___x_4107_);
lean_dec(v_x_4063_);
v_x_4062_ = v_fn_4106_;
v_x_4063_ = v___x_4108_;
goto _start;
}
case 10:
{
lean_object* v_expr_4110_; 
v_expr_4110_ = lean_ctor_get(v_x_4062_, 1);
lean_inc_ref(v_expr_4110_);
lean_dec_ref_known(v_x_4062_, 2);
v_x_4062_ = v_expr_4110_;
goto _start;
}
case 8:
{
lean_object* v_body_4112_; 
v_body_4112_ = lean_ctor_get(v_x_4062_, 3);
lean_inc_ref(v_body_4112_);
lean_dec_ref_known(v_x_4062_, 4);
v_x_4062_ = v_body_4112_;
goto _start;
}
case 6:
{
lean_object* v_body_4114_; lean_object* v_zero_4115_; uint8_t v_isZero_4116_; 
v_body_4114_ = lean_ctor_get(v_x_4062_, 2);
lean_inc_ref(v_body_4114_);
lean_dec_ref_known(v_x_4062_, 3);
v_zero_4115_ = lean_unsigned_to_nat(0u);
v_isZero_4116_ = lean_nat_dec_eq(v_x_4063_, v_zero_4115_);
if (v_isZero_4116_ == 1)
{
uint8_t v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_dec_ref(v_body_4114_);
lean_dec(v_x_4063_);
v___x_4117_ = 0;
v___x_4118_ = lean_box(v___x_4117_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
return v___x_4119_;
}
else
{
lean_object* v_one_4120_; lean_object* v_n_4121_; 
v_one_4120_ = lean_unsigned_to_nat(1u);
v_n_4121_ = lean_nat_sub(v_x_4063_, v_one_4120_);
lean_dec(v_x_4063_);
v_x_4062_ = v_body_4114_;
v_x_4063_ = v_n_4121_;
goto _start;
}
}
default: 
{
uint8_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_dec(v_x_4063_);
lean_dec_ref(v_x_4062_);
v___x_4123_ = 2;
v___x_4124_ = lean_box(v___x_4123_);
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
return v___x_4125_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
switch(lean_obj_tag(v_x_4134_))
{
case 0:
{
uint8_t v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec_ref_known(v_x_4134_, 1);
v___x_4140_ = 2;
v___x_4141_ = lean_box(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
return v___x_4142_;
}
case 1:
{
lean_object* v_fvarId_4143_; lean_object* v___x_4144_; 
v_fvarId_4143_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_fvarId_4143_);
lean_dec_ref_known(v_x_4134_, 1);
v___x_4144_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4143_, v_a_4135_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4144_, 1);
v___x_4146_ = lean_unsigned_to_nat(0u);
v___x_4147_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4145_, v___x_4146_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4147_;
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
v_a_4148_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4144_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4144_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4156_; lean_object* v___x_4157_; 
v_mvarId_4156_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_mvarId_4156_);
lean_dec_ref_known(v_x_4134_, 1);
v___x_4157_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4156_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4158_, v___x_4159_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4160_;
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
v_a_4161_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4157_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4157_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
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
case 7:
{
lean_object* v_body_4186_; 
v_body_4186_ = lean_ctor_get(v_x_4134_, 2);
lean_inc_ref(v_body_4186_);
lean_dec_ref_known(v_x_4134_, 3);
v_x_4134_ = v_body_4186_;
goto _start;
}
case 8:
{
lean_object* v_body_4188_; 
v_body_4188_ = lean_ctor_get(v_x_4134_, 3);
lean_inc_ref(v_body_4188_);
lean_dec_ref_known(v_x_4134_, 4);
v_x_4134_ = v_body_4188_;
goto _start;
}
case 10:
{
lean_object* v_expr_4190_; 
v_expr_4190_ = lean_ctor_get(v_x_4134_, 1);
lean_inc_ref(v_expr_4190_);
lean_dec_ref_known(v_x_4134_, 2);
v_x_4134_ = v_expr_4190_;
goto _start;
}
case 11:
{
uint8_t v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_dec_ref_known(v_x_4134_, 3);
v___x_4192_ = 2;
v___x_4193_ = lean_box(v___x_4192_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
default: 
{
uint8_t v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_dec_ref(v_x_4134_);
v___x_4195_ = 0;
v___x_4196_ = lean_box(v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_Meta_isPropQuick(v_x_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
lean_dec(v_a_4202_);
lean_dec_ref(v_a_4201_);
lean_dec(v_a_4200_);
lean_dec_ref(v_a_4199_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v___x_4211_; 
lean_inc_ref(v_e_4205_);
v___x_4211_ = l_Lean_Meta_isPropQuick(v_e_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4268_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4214_ = v___x_4211_;
v_isShared_4215_ = v_isSharedCheck_4268_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4211_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4268_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
uint8_t v___x_4216_; 
v___x_4216_ = lean_unbox(v_a_4212_);
lean_dec(v_a_4212_);
switch(v___x_4216_)
{
case 0:
{
uint8_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4220_; 
lean_dec_ref(v_e_4205_);
v___x_4217_ = 0;
v___x_4218_ = lean_box(v___x_4217_);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4218_);
v___x_4220_ = v___x_4214_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
case 1:
{
uint8_t v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4225_; 
lean_dec_ref(v_e_4205_);
v___x_4222_ = 1;
v___x_4223_ = lean_box(v___x_4222_);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4223_);
v___x_4225_ = v___x_4214_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
default: 
{
lean_object* v___x_4227_; 
lean_del_object(v___x_4214_);
lean_inc(v_a_4209_);
lean_inc_ref(v_a_4208_);
lean_inc(v_a_4207_);
lean_inc_ref(v_a_4206_);
v___x_4227_ = lean_infer_type(v_e_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = l_Lean_Meta_whnfD(v_a_4228_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4251_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4251_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4251_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
if (lean_obj_tag(v_a_4230_) == 3)
{
lean_object* v_u_4234_; lean_object* v___x_4235_; lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4245_; 
lean_del_object(v___x_4232_);
v_u_4234_ = lean_ctor_get(v_a_4230_, 0);
lean_inc(v_u_4234_);
lean_dec_ref_known(v_a_4230_, 1);
v___x_4235_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4234_, v_a_4207_);
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4245_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4245_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4240_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4236_);
lean_dec(v_a_4236_);
v___x_4241_ = lean_box(v___x_4240_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v___x_4241_);
v___x_4243_ = v___x_4238_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
else
{
uint8_t v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4249_; 
lean_dec(v_a_4230_);
v___x_4246_ = 0;
v___x_4247_ = lean_box(v___x_4246_);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4247_);
v___x_4249_ = v___x_4232_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
v_a_4252_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4229_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4229_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
v_a_4260_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4227_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4227_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v_e_4205_);
v_a_4269_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4211_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4211_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_Meta_isProp(v_e_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4284_){
_start:
{
switch(lean_obj_tag(v_x_4284_))
{
case 0:
{
lean_object* v___x_4285_; 
v___x_4285_ = lean_unsigned_to_nat(0u);
return v___x_4285_;
}
case 1:
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_unsigned_to_nat(1u);
return v___x_4286_;
}
case 2:
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_unsigned_to_nat(2u);
return v___x_4287_;
}
default: 
{
lean_object* v___x_4288_; 
v___x_4288_ = lean_unsigned_to_nat(3u);
return v___x_4288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4289_);
lean_dec(v_x_4289_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4291_, lean_object* v_k_4292_){
_start:
{
if (lean_obj_tag(v_t_4291_) == 3)
{
lean_object* v_idx_4293_; lean_object* v___x_4294_; 
v_idx_4293_ = lean_ctor_get(v_t_4291_, 0);
lean_inc(v_idx_4293_);
lean_dec_ref_known(v_t_4291_, 1);
v___x_4294_ = lean_apply_1(v_k_4292_, v_idx_4293_);
return v___x_4294_;
}
else
{
lean_dec(v_t_4291_);
return v_k_4292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4295_, lean_object* v_ctorIdx_4296_, lean_object* v_t_4297_, lean_object* v_h_4298_, lean_object* v_k_4299_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4297_, v_k_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4301_, lean_object* v_ctorIdx_4302_, lean_object* v_t_4303_, lean_object* v_h_4304_, lean_object* v_k_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4301_, v_ctorIdx_4302_, v_t_4303_, v_h_4304_, v_k_4305_);
lean_dec(v_ctorIdx_4302_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4307_, lean_object* v_false_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4307_, v_false_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4310_, lean_object* v_t_4311_, lean_object* v_h_4312_, lean_object* v_false_4313_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4311_, v_false_4313_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4315_, lean_object* v_true_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4315_, v_true_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4318_, lean_object* v_t_4319_, lean_object* v_h_4320_, lean_object* v_true_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4319_, v_true_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4323_, lean_object* v_undef_4324_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4323_, v_undef_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4326_, lean_object* v_t_4327_, lean_object* v_h_4328_, lean_object* v_undef_4329_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4327_, v_undef_4329_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4331_, lean_object* v_bvar_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4331_, v_bvar_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4334_, lean_object* v_t_4335_, lean_object* v_h_4336_, lean_object* v_bvar_4337_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4335_, v_bvar_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4339_){
_start:
{
switch(v_x_4339_)
{
case 0:
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_box(0);
return v___x_4340_;
}
case 1:
{
lean_object* v___x_4341_; 
v___x_4341_ = lean_box(1);
return v___x_4341_;
}
default: 
{
lean_object* v___x_4342_; 
v___x_4342_ = lean_box(2);
return v___x_4342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4343_){
_start:
{
uint8_t v_x_25__boxed_4344_; lean_object* v_res_4345_; 
v_x_25__boxed_4344_ = lean_unbox(v_x_4343_);
v_res_4345_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4344_);
return v_res_4345_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4346_){
_start:
{
switch(lean_obj_tag(v_x_4346_))
{
case 0:
{
uint8_t v___x_4347_; 
v___x_4347_ = 0;
return v___x_4347_;
}
case 1:
{
uint8_t v___x_4348_; 
v___x_4348_ = 1;
return v___x_4348_;
}
default: 
{
uint8_t v___x_4349_; 
v___x_4349_ = 2;
return v___x_4349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4350_){
_start:
{
uint8_t v_res_4351_; lean_object* v_r_4352_; 
v_res_4351_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4350_);
lean_dec(v_x_4350_);
v_r_4352_ = lean_box(v_res_4351_);
return v_r_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4354_){
_start:
{
switch(lean_obj_tag(v_e_4354_))
{
case 3:
{
lean_object* v_u_4355_; uint8_t v___x_4356_; 
v_u_4355_ = lean_ctor_get(v_e_4354_, 0);
v___x_4356_ = l_Lean_Level_isNeverZero(v_u_4355_);
if (v___x_4356_ == 0)
{
uint8_t v___x_4357_; 
v___x_4357_ = l_Lean_Level_isZero(v_u_4355_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; 
v___x_4358_ = lean_box(2);
return v___x_4358_;
}
else
{
lean_object* v___x_4359_; 
v___x_4359_ = lean_box(1);
return v___x_4359_;
}
}
else
{
lean_object* v___x_4360_; 
v___x_4360_ = lean_box(0);
return v___x_4360_;
}
}
case 5:
{
lean_object* v_fn_4361_; 
v_fn_4361_ = lean_ctor_get(v_e_4354_, 0);
if (lean_obj_tag(v_fn_4361_) == 4)
{
lean_object* v_declName_4362_; 
v_declName_4362_ = lean_ctor_get(v_fn_4361_, 0);
if (lean_obj_tag(v_declName_4362_) == 1)
{
lean_object* v_pre_4363_; 
v_pre_4363_ = lean_ctor_get(v_declName_4362_, 0);
if (lean_obj_tag(v_pre_4363_) == 0)
{
lean_object* v_arg_4364_; lean_object* v_str_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; 
v_arg_4364_ = lean_ctor_get(v_e_4354_, 1);
v_str_4365_ = lean_ctor_get(v_declName_4362_, 1);
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4367_ = lean_string_dec_eq(v_str_4365_, v___x_4366_);
if (v___x_4367_ == 0)
{
lean_object* v___x_4368_; 
v___x_4368_ = lean_box(2);
return v___x_4368_;
}
else
{
v_e_4354_ = v_arg_4364_;
goto _start;
}
}
else
{
lean_object* v___x_4370_; 
v___x_4370_ = lean_box(2);
return v___x_4370_;
}
}
else
{
lean_object* v___x_4371_; 
v___x_4371_ = lean_box(2);
return v___x_4371_;
}
}
else
{
lean_object* v___x_4372_; 
v___x_4372_ = lean_box(2);
return v___x_4372_;
}
}
default: 
{
lean_object* v___x_4373_; 
v___x_4373_ = lean_box(2);
return v___x_4373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4374_);
lean_dec_ref(v_e_4374_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4376_, lean_object* v_binderType_4377_){
_start:
{
if (lean_obj_tag(v_r_4376_) == 3)
{
lean_object* v_idx_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4390_; 
v_idx_4378_ = lean_ctor_get(v_r_4376_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_r_4376_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4380_ = v_r_4376_;
v_isShared_4381_ = v_isSharedCheck_4390_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_idx_4378_);
lean_dec(v_r_4376_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4390_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v_zero_4382_; uint8_t v_isZero_4383_; 
v_zero_4382_ = lean_unsigned_to_nat(0u);
v_isZero_4383_ = lean_nat_dec_eq(v_idx_4378_, v_zero_4382_);
if (v_isZero_4383_ == 1)
{
lean_object* v___x_4384_; 
lean_del_object(v___x_4380_);
lean_dec(v_idx_4378_);
v___x_4384_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4377_);
return v___x_4384_;
}
else
{
lean_object* v_one_4385_; lean_object* v_n_4386_; lean_object* v___x_4388_; 
v_one_4385_ = lean_unsigned_to_nat(1u);
v_n_4386_ = lean_nat_sub(v_idx_4378_, v_one_4385_);
lean_dec(v_idx_4378_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v_n_4386_);
v___x_4388_ = v___x_4380_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_n_4386_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
return v_r_4376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4391_, lean_object* v_binderType_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4391_, v_binderType_4392_);
lean_dec_ref(v_binderType_4392_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4394_, lean_object* v_x_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_){
_start:
{
lean_object* v_type_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; 
switch(lean_obj_tag(v_x_4394_))
{
case 7:
{
lean_object* v_binderType_4429_; lean_object* v_body_4430_; lean_object* v_zero_4431_; uint8_t v_isZero_4432_; 
v_binderType_4429_ = lean_ctor_get(v_x_4394_, 1);
v_body_4430_ = lean_ctor_get(v_x_4394_, 2);
v_zero_4431_ = lean_unsigned_to_nat(0u);
v_isZero_4432_ = lean_nat_dec_eq(v_x_4395_, v_zero_4431_);
if (v_isZero_4432_ == 1)
{
v_type_4402_ = v_x_4394_;
v___y_4403_ = v_a_4396_;
v___y_4404_ = v_a_4397_;
v___y_4405_ = v_a_4398_;
v___y_4406_ = v_a_4399_;
goto v___jp_4401_;
}
else
{
lean_object* v_one_4433_; lean_object* v_n_4434_; lean_object* v___x_4435_; 
lean_inc_ref(v_body_4430_);
lean_inc_ref(v_binderType_4429_);
lean_dec_ref_known(v_x_4394_, 3);
v_one_4433_ = lean_unsigned_to_nat(1u);
v_n_4434_ = lean_nat_sub(v_x_4395_, v_one_4433_);
v___x_4435_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4430_, v_n_4434_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_);
lean_dec(v_n_4434_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4444_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4444_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4444_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4440_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4436_, v_binderType_4429_);
lean_dec_ref(v_binderType_4429_);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4440_);
v___x_4442_ = v___x_4438_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
else
{
lean_dec_ref(v_binderType_4429_);
return v___x_4435_;
}
}
}
case 8:
{
lean_object* v_type_4445_; lean_object* v_body_4446_; lean_object* v___x_4447_; 
v_type_4445_ = lean_ctor_get(v_x_4394_, 1);
lean_inc_ref(v_type_4445_);
v_body_4446_ = lean_ctor_get(v_x_4394_, 3);
lean_inc_ref(v_body_4446_);
lean_dec_ref_known(v_x_4394_, 4);
v___x_4447_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4446_, v_x_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4456_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4450_ = v___x_4447_;
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4447_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4452_; lean_object* v___x_4454_; 
v___x_4452_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4448_, v_type_4445_);
lean_dec_ref(v_type_4445_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 0, v___x_4452_);
v___x_4454_ = v___x_4450_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
else
{
lean_dec_ref(v_type_4445_);
return v___x_4447_;
}
}
case 10:
{
lean_object* v_expr_4457_; 
v_expr_4457_ = lean_ctor_get(v_x_4394_, 1);
lean_inc_ref(v_expr_4457_);
lean_dec_ref_known(v_x_4394_, 2);
v_x_4394_ = v_expr_4457_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4459_; lean_object* v___x_4460_; uint8_t v___x_4461_; 
v_deBruijnIndex_4459_ = lean_ctor_get(v_x_4394_, 0);
lean_inc(v_deBruijnIndex_4459_);
lean_dec_ref_known(v_x_4394_, 1);
v___x_4460_ = lean_unsigned_to_nat(0u);
v___x_4461_ = lean_nat_dec_eq(v_x_4395_, v___x_4460_);
if (v___x_4461_ == 0)
{
lean_dec(v_deBruijnIndex_4459_);
goto v___jp_4426_;
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4462_, 0, v_deBruijnIndex_4459_);
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
return v___x_4463_;
}
}
default: 
{
lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4464_ = lean_unsigned_to_nat(0u);
v___x_4465_ = lean_nat_dec_eq(v_x_4395_, v___x_4464_);
if (v___x_4465_ == 0)
{
lean_dec_ref(v_x_4394_);
goto v___jp_4426_;
}
else
{
v_type_4402_ = v_x_4394_;
v___y_4403_ = v_a_4396_;
v___y_4404_ = v_a_4397_;
v___y_4405_ = v_a_4398_;
v___y_4406_ = v_a_4399_;
goto v___jp_4401_;
}
}
}
v___jp_4401_:
{
lean_object* v___x_4407_; 
v___x_4407_ = l_Lean_Meta_isPropQuick(v_type_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4417_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4417_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4417_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
uint8_t v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4412_ = lean_unbox(v_a_4408_);
lean_dec(v_a_4408_);
v___x_4413_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4412_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v___x_4413_);
v___x_4415_ = v___x_4410_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
v_a_4418_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4407_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4407_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
v___jp_4426_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_box(2);
v___x_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
return v___x_4428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4466_, lean_object* v_x_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4466_, v_x_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_);
lean_dec(v_a_4471_);
lean_dec_ref(v_a_4470_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_x_4467_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4474_, lean_object* v_n_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4474_, v_n_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4491_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
uint8_t v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4486_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4482_);
lean_dec(v_a_4482_);
v___x_4487_ = lean_box(v___x_4486_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4487_);
v___x_4489_ = v___x_4484_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
v_a_4492_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4481_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4481_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4500_, lean_object* v_n_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4500_, v_n_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_n_4501_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4508_, lean_object* v_x_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_){
_start:
{
switch(lean_obj_tag(v_x_4508_))
{
case 4:
{
lean_object* v_declName_4515_; lean_object* v_us_4516_; lean_object* v___x_4517_; 
v_declName_4515_ = lean_ctor_get(v_x_4508_, 0);
lean_inc(v_declName_4515_);
v_us_4516_ = lean_ctor_get(v_x_4508_, 1);
lean_inc(v_us_4516_);
lean_dec_ref_known(v_x_4508_, 2);
v___x_4517_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4515_, v_us_4516_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
v___x_4519_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4518_, v_x_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_x_4509_);
return v___x_4519_;
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
lean_dec(v_x_4509_);
v_a_4520_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4517_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4517_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4528_; lean_object* v___x_4529_; 
v_fvarId_4528_ = lean_ctor_get(v_x_4508_, 0);
lean_inc(v_fvarId_4528_);
lean_dec_ref_known(v_x_4508_, 1);
v___x_4529_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4528_, v_a_4510_, v_a_4512_, v_a_4513_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4531_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v___x_4531_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4530_, v_x_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_x_4509_);
return v___x_4531_;
}
else
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
lean_dec(v_x_4509_);
v_a_4532_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4529_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4529_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4540_; lean_object* v___x_4541_; 
v_mvarId_4540_ = lean_ctor_get(v_x_4508_, 0);
lean_inc(v_mvarId_4540_);
lean_dec_ref_known(v_x_4508_, 1);
v___x_4541_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4540_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4543_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___x_4543_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4542_, v_x_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
lean_dec(v_x_4509_);
return v___x_4543_;
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_x_4509_);
v_a_4544_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4541_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4541_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
case 5:
{
lean_object* v_fn_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_fn_4552_ = lean_ctor_get(v_x_4508_, 0);
lean_inc_ref(v_fn_4552_);
lean_dec_ref_known(v_x_4508_, 2);
v___x_4553_ = lean_unsigned_to_nat(1u);
v___x_4554_ = lean_nat_add(v_x_4509_, v___x_4553_);
lean_dec(v_x_4509_);
v_x_4508_ = v_fn_4552_;
v_x_4509_ = v___x_4554_;
goto _start;
}
case 10:
{
lean_object* v_expr_4556_; 
v_expr_4556_ = lean_ctor_get(v_x_4508_, 1);
lean_inc_ref(v_expr_4556_);
lean_dec_ref_known(v_x_4508_, 2);
v_x_4508_ = v_expr_4556_;
goto _start;
}
case 8:
{
lean_object* v_body_4558_; 
v_body_4558_ = lean_ctor_get(v_x_4508_, 3);
lean_inc_ref(v_body_4558_);
lean_dec_ref_known(v_x_4508_, 4);
v_x_4508_ = v_body_4558_;
goto _start;
}
case 6:
{
lean_object* v_body_4560_; lean_object* v_zero_4561_; uint8_t v_isZero_4562_; 
v_body_4560_ = lean_ctor_get(v_x_4508_, 2);
lean_inc_ref(v_body_4560_);
lean_dec_ref_known(v_x_4508_, 3);
v_zero_4561_ = lean_unsigned_to_nat(0u);
v_isZero_4562_ = lean_nat_dec_eq(v_x_4509_, v_zero_4561_);
if (v_isZero_4562_ == 1)
{
lean_object* v___x_4563_; 
lean_dec(v_x_4509_);
v___x_4563_ = l_Lean_Meta_isProofQuick(v_body_4560_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_);
return v___x_4563_;
}
else
{
lean_object* v_one_4564_; lean_object* v_n_4565_; 
v_one_4564_ = lean_unsigned_to_nat(1u);
v_n_4565_ = lean_nat_sub(v_x_4509_, v_one_4564_);
lean_dec(v_x_4509_);
v_x_4508_ = v_body_4560_;
v_x_4509_ = v_n_4565_;
goto _start;
}
}
default: 
{
uint8_t v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
lean_dec(v_x_4509_);
lean_dec_ref(v_x_4508_);
v___x_4567_ = 2;
v___x_4568_ = lean_box(v___x_4567_);
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
return v___x_4569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
switch(lean_obj_tag(v_x_4570_))
{
case 0:
{
uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
lean_dec_ref_known(v_x_4570_, 1);
v___x_4576_ = 2;
v___x_4577_ = lean_box(v___x_4576_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
return v___x_4578_;
}
case 1:
{
lean_object* v_fvarId_4579_; lean_object* v___x_4580_; 
v_fvarId_4579_ = lean_ctor_get(v_x_4570_, 0);
lean_inc(v_fvarId_4579_);
lean_dec_ref_known(v_x_4570_, 1);
v___x_4580_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4579_, v_a_4571_, v_a_4573_, v_a_4574_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref_known(v___x_4580_, 1);
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4581_, v___x_4582_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4583_;
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
v_a_4584_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4580_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4580_);
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
case 2:
{
lean_object* v_mvarId_4592_; lean_object* v___x_4593_; 
v_mvarId_4592_ = lean_ctor_get(v_x_4570_, 0);
lean_inc(v_mvarId_4592_);
lean_dec_ref_known(v_x_4570_, 1);
v___x_4593_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4592_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref_known(v___x_4593_, 1);
v___x_4595_ = lean_unsigned_to_nat(0u);
v___x_4596_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4594_, v___x_4595_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4596_;
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
v_a_4597_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4593_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4593_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
case 4:
{
lean_object* v_declName_4605_; lean_object* v_us_4606_; lean_object* v___x_4607_; 
v_declName_4605_ = lean_ctor_get(v_x_4570_, 0);
lean_inc(v_declName_4605_);
v_us_4606_ = lean_ctor_get(v_x_4570_, 1);
lean_inc(v_us_4606_);
lean_dec_ref_known(v_x_4570_, 2);
v___x_4607_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4605_, v_us_4606_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v___x_4607_, 1);
v___x_4609_ = lean_unsigned_to_nat(0u);
v___x_4610_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4608_, v___x_4609_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4610_;
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
v_a_4611_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4607_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4607_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
case 5:
{
lean_object* v_fn_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v_fn_4619_ = lean_ctor_get(v_x_4570_, 0);
lean_inc_ref(v_fn_4619_);
lean_dec_ref_known(v_x_4570_, 2);
v___x_4620_ = lean_unsigned_to_nat(1u);
v___x_4621_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4619_, v___x_4620_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4621_;
}
case 6:
{
lean_object* v_body_4622_; 
v_body_4622_ = lean_ctor_get(v_x_4570_, 2);
lean_inc_ref(v_body_4622_);
lean_dec_ref_known(v_x_4570_, 3);
v_x_4570_ = v_body_4622_;
goto _start;
}
case 8:
{
lean_object* v_body_4624_; 
v_body_4624_ = lean_ctor_get(v_x_4570_, 3);
lean_inc_ref(v_body_4624_);
lean_dec_ref_known(v_x_4570_, 4);
v_x_4570_ = v_body_4624_;
goto _start;
}
case 10:
{
lean_object* v_expr_4626_; 
v_expr_4626_ = lean_ctor_get(v_x_4570_, 1);
lean_inc_ref(v_expr_4626_);
lean_dec_ref_known(v_x_4570_, 2);
v_x_4570_ = v_expr_4626_;
goto _start;
}
case 11:
{
uint8_t v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
lean_dec_ref_known(v_x_4570_, 3);
v___x_4628_ = 2;
v___x_4629_ = lean_box(v___x_4628_);
v___x_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4629_);
return v___x_4630_;
}
default: 
{
uint8_t v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
lean_dec_ref(v_x_4570_);
v___x_4631_ = 0;
v___x_4632_ = lean_box(v___x_4631_);
v___x_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
return v___x_4633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lean_Meta_isProofQuick(v_x_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4641_, lean_object* v_x_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v_res_4648_; 
v_res_4648_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4641_, v_x_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v___x_4655_; 
lean_inc_ref(v_e_4649_);
v___x_4655_ = l_Lean_Meta_isProofQuick(v_e_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4682_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4658_ = v___x_4655_;
v_isShared_4659_ = v_isSharedCheck_4682_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4655_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4682_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
uint8_t v___x_4660_; 
v___x_4660_ = lean_unbox(v_a_4656_);
lean_dec(v_a_4656_);
switch(v___x_4660_)
{
case 0:
{
uint8_t v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
lean_dec_ref(v_e_4649_);
v___x_4661_ = 0;
v___x_4662_ = lean_box(v___x_4661_);
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4662_);
v___x_4664_ = v___x_4658_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
case 1:
{
uint8_t v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4669_; 
lean_dec_ref(v_e_4649_);
v___x_4666_ = 1;
v___x_4667_ = lean_box(v___x_4666_);
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v___x_4667_);
v___x_4669_ = v___x_4658_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4667_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
default: 
{
lean_object* v___x_4671_; 
lean_del_object(v___x_4658_);
lean_inc(v_a_4653_);
lean_inc_ref(v_a_4652_);
lean_inc(v_a_4651_);
lean_inc_ref(v_a_4650_);
v___x_4671_ = lean_infer_type(v_e_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4673_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v___x_4673_ = l_Lean_Meta_isProp(v_a_4672_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
return v___x_4673_;
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
v_a_4674_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4671_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4671_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
lean_dec_ref(v_e_4649_);
v_a_4683_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4655_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4655_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_Meta_isProof(v_e_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4698_, lean_object* v_x_4699_){
_start:
{
switch(lean_obj_tag(v_x_4698_))
{
case 3:
{
lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4705_ = lean_unsigned_to_nat(0u);
v___x_4706_ = lean_nat_dec_eq(v_x_4699_, v___x_4705_);
lean_dec(v_x_4699_);
if (v___x_4706_ == 0)
{
goto v___jp_4701_;
}
else
{
uint8_t v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4707_ = 1;
v___x_4708_ = lean_box(v___x_4707_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
}
case 7:
{
lean_object* v_body_4710_; lean_object* v_zero_4711_; uint8_t v_isZero_4712_; 
v_body_4710_ = lean_ctor_get(v_x_4698_, 2);
v_zero_4711_ = lean_unsigned_to_nat(0u);
v_isZero_4712_ = lean_nat_dec_eq(v_x_4699_, v_zero_4711_);
if (v_isZero_4712_ == 1)
{
uint8_t v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
lean_dec(v_x_4699_);
v___x_4713_ = 0;
v___x_4714_ = lean_box(v___x_4713_);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
return v___x_4715_;
}
else
{
lean_object* v_one_4716_; lean_object* v_n_4717_; 
v_one_4716_ = lean_unsigned_to_nat(1u);
v_n_4717_ = lean_nat_sub(v_x_4699_, v_one_4716_);
lean_dec(v_x_4699_);
v_x_4698_ = v_body_4710_;
v_x_4699_ = v_n_4717_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4719_; 
v_body_4719_ = lean_ctor_get(v_x_4698_, 3);
v_x_4698_ = v_body_4719_;
goto _start;
}
case 10:
{
lean_object* v_expr_4721_; 
v_expr_4721_ = lean_ctor_get(v_x_4698_, 1);
v_x_4698_ = v_expr_4721_;
goto _start;
}
default: 
{
lean_dec(v_x_4699_);
goto v___jp_4701_;
}
}
v___jp_4701_:
{
uint8_t v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = 2;
v___x_4703_ = lean_box(v___x_4702_);
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
return v___x_4704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4723_, lean_object* v_x_4724_, lean_object* v_a_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4723_, v_x_4724_);
lean_dec_ref(v_x_4723_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4727_, lean_object* v_x_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_){
_start:
{
lean_object* v___x_4734_; 
v___x_4734_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4727_, v_x_4728_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4735_, lean_object* v_x_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4735_, v_x_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_);
lean_dec(v_a_4740_);
lean_dec_ref(v_a_4739_);
lean_dec(v_a_4738_);
lean_dec_ref(v_a_4737_);
lean_dec_ref(v_x_4735_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4743_, lean_object* v_x_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
switch(lean_obj_tag(v_x_4743_))
{
case 4:
{
lean_object* v_declName_4750_; lean_object* v_us_4751_; lean_object* v___x_4752_; 
v_declName_4750_ = lean_ctor_get(v_x_4743_, 0);
lean_inc(v_declName_4750_);
v_us_4751_ = lean_ctor_get(v_x_4743_, 1);
lean_inc(v_us_4751_);
lean_dec_ref_known(v_x_4743_, 2);
v___x_4752_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4750_, v_us_4751_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4754_; 
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_a_4753_);
lean_dec_ref_known(v___x_4752_, 1);
v___x_4754_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4753_, v_x_4744_);
lean_dec(v_a_4753_);
return v___x_4754_;
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_dec(v_x_4744_);
v_a_4755_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4752_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4752_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4763_; lean_object* v___x_4764_; 
v_fvarId_4763_ = lean_ctor_get(v_x_4743_, 0);
lean_inc(v_fvarId_4763_);
lean_dec_ref_known(v_x_4743_, 1);
v___x_4764_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4763_, v_a_4745_, v_a_4747_, v_a_4748_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4766_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4766_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4765_, v_x_4744_);
lean_dec(v_a_4765_);
return v___x_4766_;
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
lean_dec(v_x_4744_);
v_a_4767_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4764_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4764_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4775_; lean_object* v___x_4776_; 
v_mvarId_4775_ = lean_ctor_get(v_x_4743_, 0);
lean_inc(v_mvarId_4775_);
lean_dec_ref_known(v_x_4743_, 1);
v___x_4776_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4775_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4778_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref_known(v___x_4776_, 1);
v___x_4778_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4777_, v_x_4744_);
lean_dec(v_a_4777_);
return v___x_4778_;
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
lean_dec(v_x_4744_);
v_a_4779_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4776_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4776_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
case 5:
{
lean_object* v_fn_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
v_fn_4787_ = lean_ctor_get(v_x_4743_, 0);
lean_inc_ref(v_fn_4787_);
lean_dec_ref_known(v_x_4743_, 2);
v___x_4788_ = lean_unsigned_to_nat(1u);
v___x_4789_ = lean_nat_add(v_x_4744_, v___x_4788_);
lean_dec(v_x_4744_);
v_x_4743_ = v_fn_4787_;
v_x_4744_ = v___x_4789_;
goto _start;
}
case 10:
{
lean_object* v_expr_4791_; 
v_expr_4791_ = lean_ctor_get(v_x_4743_, 1);
lean_inc_ref(v_expr_4791_);
lean_dec_ref_known(v_x_4743_, 2);
v_x_4743_ = v_expr_4791_;
goto _start;
}
case 8:
{
lean_object* v_body_4793_; 
v_body_4793_ = lean_ctor_get(v_x_4743_, 3);
lean_inc_ref(v_body_4793_);
lean_dec_ref_known(v_x_4743_, 4);
v_x_4743_ = v_body_4793_;
goto _start;
}
case 6:
{
lean_object* v_body_4795_; lean_object* v_zero_4796_; uint8_t v_isZero_4797_; 
v_body_4795_ = lean_ctor_get(v_x_4743_, 2);
lean_inc_ref(v_body_4795_);
lean_dec_ref_known(v_x_4743_, 3);
v_zero_4796_ = lean_unsigned_to_nat(0u);
v_isZero_4797_ = lean_nat_dec_eq(v_x_4744_, v_zero_4796_);
if (v_isZero_4797_ == 1)
{
uint8_t v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
lean_dec_ref(v_body_4795_);
lean_dec(v_x_4744_);
v___x_4798_ = 0;
v___x_4799_ = lean_box(v___x_4798_);
v___x_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
return v___x_4800_;
}
else
{
lean_object* v_one_4801_; lean_object* v_n_4802_; 
v_one_4801_ = lean_unsigned_to_nat(1u);
v_n_4802_ = lean_nat_sub(v_x_4744_, v_one_4801_);
lean_dec(v_x_4744_);
v_x_4743_ = v_body_4795_;
v_x_4744_ = v_n_4802_;
goto _start;
}
}
default: 
{
uint8_t v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
lean_dec(v_x_4744_);
lean_dec_ref(v_x_4743_);
v___x_4804_ = 2;
v___x_4805_ = lean_box(v___x_4804_);
v___x_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
return v___x_4806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4807_, lean_object* v_x_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4807_, v_x_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_){
_start:
{
switch(lean_obj_tag(v_x_4815_))
{
case 1:
{
lean_object* v_fvarId_4821_; lean_object* v___x_4822_; 
v_fvarId_4821_ = lean_ctor_get(v_x_4815_, 0);
lean_inc(v_fvarId_4821_);
lean_dec_ref_known(v_x_4815_, 1);
v___x_4822_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4821_, v_a_4816_, v_a_4818_, v_a_4819_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v___x_4824_ = lean_unsigned_to_nat(0u);
v___x_4825_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4823_, v___x_4824_);
lean_dec(v_a_4823_);
return v___x_4825_;
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
v_a_4826_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4822_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4822_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4834_; lean_object* v___x_4835_; 
v_mvarId_4834_ = lean_ctor_get(v_x_4815_, 0);
lean_inc(v_mvarId_4834_);
lean_dec_ref_known(v_x_4815_, 1);
v___x_4835_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4834_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref_known(v___x_4835_, 1);
v___x_4837_ = lean_unsigned_to_nat(0u);
v___x_4838_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4836_, v___x_4837_);
lean_dec(v_a_4836_);
return v___x_4838_;
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4835_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4835_);
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
case 3:
{
uint8_t v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
lean_dec_ref_known(v_x_4815_, 1);
v___x_4847_ = 1;
v___x_4848_ = lean_box(v___x_4847_);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
case 4:
{
lean_object* v_declName_4850_; lean_object* v_us_4851_; lean_object* v___x_4852_; 
v_declName_4850_ = lean_ctor_get(v_x_4815_, 0);
lean_inc(v_declName_4850_);
v_us_4851_ = lean_ctor_get(v_x_4815_, 1);
lean_inc(v_us_4851_);
lean_dec_ref_known(v_x_4815_, 2);
v___x_4852_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4850_, v_us_4851_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref_known(v___x_4852_, 1);
v___x_4854_ = lean_unsigned_to_nat(0u);
v___x_4855_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4853_, v___x_4854_);
lean_dec(v_a_4853_);
return v___x_4855_;
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
v_a_4856_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4852_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4852_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
case 5:
{
lean_object* v_fn_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v_fn_4864_ = lean_ctor_get(v_x_4815_, 0);
lean_inc_ref(v_fn_4864_);
lean_dec_ref_known(v_x_4815_, 2);
v___x_4865_ = lean_unsigned_to_nat(1u);
v___x_4866_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4864_, v___x_4865_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
return v___x_4866_;
}
case 6:
{
uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
lean_dec_ref_known(v_x_4815_, 3);
v___x_4867_ = 0;
v___x_4868_ = lean_box(v___x_4867_);
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
return v___x_4869_;
}
case 7:
{
uint8_t v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
lean_dec_ref_known(v_x_4815_, 3);
v___x_4870_ = 1;
v___x_4871_ = lean_box(v___x_4870_);
v___x_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
return v___x_4872_;
}
case 8:
{
lean_object* v_body_4873_; 
v_body_4873_ = lean_ctor_get(v_x_4815_, 3);
lean_inc_ref(v_body_4873_);
lean_dec_ref_known(v_x_4815_, 4);
v_x_4815_ = v_body_4873_;
goto _start;
}
case 9:
{
uint8_t v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
lean_dec_ref_known(v_x_4815_, 1);
v___x_4875_ = 0;
v___x_4876_ = lean_box(v___x_4875_);
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
return v___x_4877_;
}
case 10:
{
lean_object* v_expr_4878_; 
v_expr_4878_ = lean_ctor_get(v_x_4815_, 1);
lean_inc_ref(v_expr_4878_);
lean_dec_ref_known(v_x_4815_, 2);
v_x_4815_ = v_expr_4878_;
goto _start;
}
default: 
{
uint8_t v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_dec_ref(v_x_4815_);
v___x_4880_ = 2;
v___x_4881_ = lean_box(v___x_4880_);
v___x_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
return v___x_4882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l_Lean_Meta_isTypeQuick(v_x_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
lean_dec(v_a_4887_);
lean_dec_ref(v_a_4886_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v___x_4896_; 
lean_inc_ref(v_e_4890_);
v___x_4896_ = l_Lean_Meta_isTypeQuick(v_e_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4946_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4946_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4946_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
uint8_t v___x_4901_; 
v___x_4901_ = lean_unbox(v_a_4897_);
lean_dec(v_a_4897_);
switch(v___x_4901_)
{
case 0:
{
uint8_t v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4905_; 
lean_dec_ref(v_e_4890_);
v___x_4902_ = 0;
v___x_4903_ = lean_box(v___x_4902_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4903_);
v___x_4905_ = v___x_4899_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
case 1:
{
uint8_t v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4910_; 
lean_dec_ref(v_e_4890_);
v___x_4907_ = 1;
v___x_4908_ = lean_box(v___x_4907_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4908_);
v___x_4910_ = v___x_4899_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
default: 
{
lean_object* v___x_4912_; 
lean_del_object(v___x_4899_);
lean_inc(v_a_4894_);
lean_inc_ref(v_a_4893_);
lean_inc(v_a_4892_);
lean_inc_ref(v_a_4891_);
v___x_4912_ = lean_infer_type(v_e_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = l_Lean_Meta_whnfD(v_a_4913_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4929_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4917_ = v___x_4914_;
v_isShared_4918_ = v_isSharedCheck_4929_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4914_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4929_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
if (lean_obj_tag(v_a_4915_) == 3)
{
uint8_t v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4922_; 
lean_dec_ref_known(v_a_4915_, 1);
v___x_4919_ = 1;
v___x_4920_ = lean_box(v___x_4919_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4920_);
v___x_4922_ = v___x_4917_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v___x_4920_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
else
{
uint8_t v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4927_; 
lean_dec(v_a_4915_);
v___x_4924_ = 0;
v___x_4925_ = lean_box(v___x_4924_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4925_);
v___x_4927_ = v___x_4917_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
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
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
v_a_4930_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4914_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4914_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
v_a_4938_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4912_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4912_);
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
}
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec_ref(v_e_4890_);
v_a_4947_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4896_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4896_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Lean_Meta_isType(v_e_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
lean_dec(v_a_4959_);
lean_dec_ref(v_a_4958_);
lean_dec(v_a_4957_);
lean_dec_ref(v_a_4956_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4962_){
_start:
{
switch(lean_obj_tag(v_x_4962_))
{
case 7:
{
lean_object* v_body_4963_; 
v_body_4963_ = lean_ctor_get(v_x_4962_, 2);
v_x_4962_ = v_body_4963_;
goto _start;
}
case 3:
{
lean_object* v_u_4965_; lean_object* v___x_4966_; 
v_u_4965_ = lean_ctor_get(v_x_4962_, 0);
lean_inc(v_u_4965_);
v___x_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4966_, 0, v_u_4965_);
return v___x_4966_;
}
default: 
{
lean_object* v___x_4967_; 
v___x_4967_ = lean_box(0);
return v___x_4967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4968_);
lean_dec_ref(v_x_4968_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4970_, lean_object* v_body_4971_, lean_object* v_x_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4970_, v_body_4971_, v_x_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4981_, lean_object* v_xs_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_){
_start:
{
switch(lean_obj_tag(v_type_4981_))
{
case 3:
{
lean_object* v_u_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
lean_dec_ref(v_xs_4982_);
v_u_4988_ = lean_ctor_get(v_type_4981_, 0);
lean_inc(v_u_4988_);
lean_dec_ref_known(v_type_4981_, 1);
v___x_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4989_, 0, v_u_4988_);
v___x_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
return v___x_4990_;
}
case 7:
{
lean_object* v_binderName_4991_; lean_object* v_binderType_4992_; lean_object* v_body_4993_; uint8_t v_binderInfo_4994_; lean_object* v___f_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; 
v_binderName_4991_ = lean_ctor_get(v_type_4981_, 0);
lean_inc(v_binderName_4991_);
v_binderType_4992_ = lean_ctor_get(v_type_4981_, 1);
lean_inc_ref(v_binderType_4992_);
v_body_4993_ = lean_ctor_get(v_type_4981_, 2);
lean_inc_ref(v_body_4993_);
v_binderInfo_4994_ = lean_ctor_get_uint8(v_type_4981_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_4981_, 3);
lean_inc_ref(v_xs_4982_);
v___f_4995_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4995_, 0, v_xs_4982_);
lean_closure_set(v___f_4995_, 1, v_body_4993_);
v___x_4996_ = lean_expr_instantiate_rev(v_binderType_4992_, v_xs_4982_);
lean_dec_ref(v_xs_4982_);
lean_dec_ref(v_binderType_4992_);
v___x_4997_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4991_, v_binderInfo_4994_, v___x_4996_, v___f_4995_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
return v___x_4997_;
}
default: 
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = lean_expr_instantiate_rev(v_type_4981_, v_xs_4982_);
lean_dec_ref(v_xs_4982_);
lean_dec_ref(v_type_4981_);
v___x_4999_ = l_Lean_Meta_whnfD(v___x_4998_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5015_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5002_ = v___x_4999_;
v_isShared_5003_ = v_isSharedCheck_5015_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4999_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5015_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
switch(lean_obj_tag(v_a_5000_))
{
case 3:
{
lean_object* v_u_5004_; lean_object* v___x_5005_; lean_object* v___x_5007_; 
v_u_5004_ = lean_ctor_get(v_a_5000_, 0);
lean_inc(v_u_5004_);
lean_dec_ref_known(v_a_5000_, 1);
v___x_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5005_, 0, v_u_5004_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v___x_5005_);
v___x_5007_ = v___x_5002_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
case 7:
{
lean_object* v___x_5009_; 
lean_del_object(v___x_5002_);
v___x_5009_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4981_ = v_a_5000_;
v_xs_4982_ = v___x_5009_;
goto _start;
}
default: 
{
lean_object* v___x_5011_; lean_object* v___x_5013_; 
lean_dec(v_a_5000_);
v___x_5011_ = lean_box(0);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v___x_5011_);
v___x_5013_ = v___x_5002_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5011_);
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
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
v_a_5016_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_4999_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_4999_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_5024_, lean_object* v_body_5025_, lean_object* v_x_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = lean_array_push(v_xs_5024_, v_x_5026_);
v___x_5033_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_5025_, v___x_5032_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_5034_, lean_object* v_xs_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5034_, v_xs_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_);
lean_dec(v_a_5039_);
lean_dec_ref(v_a_5038_);
lean_dec(v_a_5037_);
lean_dec_ref(v_a_5036_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_5042_, lean_object* v_cache_5043_, lean_object* v_a_x3f_5044_){
_start:
{
lean_object* v___x_5046_; lean_object* v_mctx_5047_; lean_object* v_zetaDeltaFVarIds_5048_; lean_object* v_postponed_5049_; lean_object* v_diag_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5060_; 
v___x_5046_ = lean_st_ref_take(v_a_5042_);
v_mctx_5047_ = lean_ctor_get(v___x_5046_, 0);
v_zetaDeltaFVarIds_5048_ = lean_ctor_get(v___x_5046_, 2);
v_postponed_5049_ = lean_ctor_get(v___x_5046_, 3);
v_diag_5050_ = lean_ctor_get(v___x_5046_, 4);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5060_ == 0)
{
lean_object* v_unused_5061_; 
v_unused_5061_ = lean_ctor_get(v___x_5046_, 1);
lean_dec(v_unused_5061_);
v___x_5052_ = v___x_5046_;
v_isShared_5053_ = v_isSharedCheck_5060_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_diag_5050_);
lean_inc(v_postponed_5049_);
lean_inc(v_zetaDeltaFVarIds_5048_);
lean_inc(v_mctx_5047_);
lean_dec(v___x_5046_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5060_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v_cache_5043_);
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_mctx_5047_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v_cache_5043_);
lean_ctor_set(v_reuseFailAlloc_5059_, 2, v_zetaDeltaFVarIds_5048_);
lean_ctor_set(v_reuseFailAlloc_5059_, 3, v_postponed_5049_);
lean_ctor_set(v_reuseFailAlloc_5059_, 4, v_diag_5050_);
v___x_5055_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5056_ = lean_st_ref_put(v_a_5042_, v___x_5055_);
v___x_5057_ = lean_box(0);
v___x_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
return v___x_5058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_5062_, lean_object* v_cache_5063_, lean_object* v_a_x3f_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5062_, v_cache_5063_, v_a_x3f_5064_);
lean_dec(v_a_x3f_5064_);
lean_dec(v_a_5062_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v___x_5073_; 
v___x_5073_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_5067_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v___x_5074_; lean_object* v_cache_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5074_ = lean_st_ref_get(v_a_5069_);
v_cache_5075_ = lean_ctor_get(v___x_5074_, 1);
lean_inc_ref(v_cache_5075_);
lean_dec(v___x_5074_);
v___x_5076_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_5077_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_5067_, v___x_5076_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v_a_5078_; lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5094_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5080_ = v___x_5077_;
v_isShared_5081_ = v_isSharedCheck_5094_;
goto v_resetjp_5079_;
}
else
{
lean_inc(v_a_5078_);
lean_dec(v___x_5077_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5094_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5083_; 
lean_inc(v_a_5078_);
if (v_isShared_5081_ == 0)
{
lean_ctor_set_tag(v___x_5080_, 1);
v___x_5083_ = v___x_5080_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5078_);
v___x_5083_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5091_; 
v___x_5084_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5069_, v_cache_5075_, v___x_5083_);
lean_dec_ref(v___x_5083_);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5091_ == 0)
{
lean_object* v_unused_5092_; 
v_unused_5092_ = lean_ctor_get(v___x_5084_, 0);
lean_dec(v_unused_5092_);
v___x_5086_ = v___x_5084_;
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
else
{
lean_dec(v___x_5084_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5089_; 
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 0, v_a_5078_);
v___x_5089_ = v___x_5086_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5078_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
v_a_5095_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5095_);
lean_dec_ref_known(v___x_5077_, 1);
v___x_5096_ = lean_box(0);
v___x_5097_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_5069_, v_cache_5075_, v___x_5096_);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; 
v_unused_5105_ = lean_ctor_get(v___x_5097_, 0);
lean_dec(v_unused_5105_);
v___x_5099_ = v___x_5097_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_dec(v___x_5097_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set_tag(v___x_5099_, 1);
lean_ctor_set(v___x_5099_, 0, v_a_5095_);
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5095_);
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
else
{
lean_object* v___x_5106_; 
lean_dec_ref(v_type_5067_);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5073_);
return v___x_5106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5114_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5135_; 
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5123_ = v___x_5120_;
v_isShared_5124_ = v_isSharedCheck_5135_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5120_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5135_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
if (lean_obj_tag(v_a_5121_) == 0)
{
uint8_t v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5128_; 
v___x_5125_ = 0;
v___x_5126_ = lean_box(v___x_5125_);
if (v_isShared_5124_ == 0)
{
lean_ctor_set(v___x_5123_, 0, v___x_5126_);
v___x_5128_ = v___x_5123_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
else
{
uint8_t v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5133_; 
lean_dec_ref_known(v_a_5121_, 1);
v___x_5130_ = 1;
v___x_5131_ = lean_box(v___x_5130_);
if (v_isShared_5124_ == 0)
{
lean_ctor_set(v___x_5123_, 0, v___x_5131_);
v___x_5133_ = v___x_5123_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v___x_5131_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
v_a_5136_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5120_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5120_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_Meta_isTypeFormerType(v_type_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec_ref(v_a_5145_);
return v_res_5150_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_5151_, lean_object* v_x_5152_){
_start:
{
if (lean_obj_tag(v_x_5151_) == 0)
{
if (lean_obj_tag(v_x_5152_) == 0)
{
uint8_t v___x_5153_; 
v___x_5153_ = 1;
return v___x_5153_;
}
else
{
uint8_t v___x_5154_; 
v___x_5154_ = 0;
return v___x_5154_;
}
}
else
{
if (lean_obj_tag(v_x_5152_) == 0)
{
uint8_t v___x_5155_; 
v___x_5155_ = 0;
return v___x_5155_;
}
else
{
lean_object* v_val_5156_; lean_object* v_val_5157_; uint8_t v___x_5158_; 
v_val_5156_ = lean_ctor_get(v_x_5151_, 0);
v_val_5157_ = lean_ctor_get(v_x_5152_, 0);
v___x_5158_ = lean_level_eq(v_val_5156_, v_val_5157_);
return v___x_5158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5159_, lean_object* v_x_5160_){
_start:
{
uint8_t v_res_5161_; lean_object* v_r_5162_; 
v_res_5161_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5159_, v_x_5160_);
lean_dec(v_x_5160_);
lean_dec(v_x_5159_);
v_r_5162_ = lean_box(v_res_5161_);
return v_r_5162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_){
_start:
{
lean_object* v___x_5171_; 
v___x_5171_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5182_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5174_ = v___x_5171_;
v_isShared_5175_ = v_isSharedCheck_5182_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5171_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5182_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5176_; uint8_t v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5180_; 
v___x_5176_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5177_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5172_, v___x_5176_);
lean_dec(v_a_5172_);
v___x_5178_ = lean_box(v___x_5177_);
if (v_isShared_5175_ == 0)
{
lean_ctor_set(v___x_5174_, 0, v___x_5178_);
v___x_5180_ = v___x_5174_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5178_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
v_a_5183_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5171_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5171_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Lean_Meta_isPropFormerType(v_type_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v___x_5204_; 
lean_inc(v_a_5202_);
lean_inc_ref(v_a_5201_);
lean_inc(v_a_5200_);
lean_inc_ref(v_a_5199_);
v___x_5204_ = lean_infer_type(v_e_5198_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_object* v_a_5205_; lean_object* v___x_5206_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
lean_inc(v_a_5205_);
lean_dec_ref_known(v___x_5204_, 1);
v___x_5206_ = l_Lean_Meta_isTypeFormerType(v_a_5205_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_);
return v___x_5206_;
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5214_; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Lean_Meta_isTypeFormer(v_e_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5222_, lean_object* v_maxFVars_x3f_5223_, lean_object* v_k_5224_, uint8_t v_cleanupAnnotations_5225_, uint8_t v_whnfType_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v___f_5232_; lean_object* v___x_5233_; 
v___f_5232_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5232_, 0, v_k_5224_);
v___x_5233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5222_, v_maxFVars_x3f_5223_, v___f_5232_, v_cleanupAnnotations_5225_, v_whnfType_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5241_; 
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5236_ = v___x_5233_;
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5233_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5234_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
v_a_5242_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5233_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5233_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5250_, lean_object* v_maxFVars_x3f_5251_, lean_object* v_k_5252_, lean_object* v_cleanupAnnotations_5253_, lean_object* v_whnfType_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5260_; uint8_t v_whnfType_boxed_5261_; lean_object* v_res_5262_; 
v_cleanupAnnotations_boxed_5260_ = lean_unbox(v_cleanupAnnotations_5253_);
v_whnfType_boxed_5261_ = lean_unbox(v_whnfType_5254_);
v_res_5262_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5250_, v_maxFVars_x3f_5251_, v_k_5252_, v_cleanupAnnotations_boxed_5260_, v_whnfType_boxed_5261_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5263_, lean_object* v_type_5264_, lean_object* v_maxFVars_x3f_5265_, lean_object* v_k_5266_, uint8_t v_cleanupAnnotations_5267_, uint8_t v_whnfType_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_){
_start:
{
lean_object* v___x_5274_; 
v___x_5274_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5264_, v_maxFVars_x3f_5265_, v_k_5266_, v_cleanupAnnotations_5267_, v_whnfType_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_);
return v___x_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5275_, lean_object* v_type_5276_, lean_object* v_maxFVars_x3f_5277_, lean_object* v_k_5278_, lean_object* v_cleanupAnnotations_5279_, lean_object* v_whnfType_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5286_; uint8_t v_whnfType_boxed_5287_; lean_object* v_res_5288_; 
v_cleanupAnnotations_boxed_5286_ = lean_unbox(v_cleanupAnnotations_5279_);
v_whnfType_boxed_5287_ = lean_unbox(v_whnfType_5280_);
v_res_5288_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5275_, v_type_5276_, v_maxFVars_x3f_5277_, v_k_5278_, v_cleanupAnnotations_boxed_5286_, v_whnfType_boxed_5287_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
return v_res_5288_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5289_, lean_object* v_as_5290_, size_t v_i_5291_, size_t v_stop_5292_){
_start:
{
uint8_t v___x_5293_; 
v___x_5293_ = lean_usize_dec_eq(v_i_5291_, v_stop_5292_);
if (v___x_5293_ == 0)
{
lean_object* v___x_5294_; uint8_t v___x_5295_; 
v___x_5294_ = lean_array_uget_borrowed(v_as_5290_, v_i_5291_);
v___x_5295_ = lean_expr_eqv(v_a_5289_, v___x_5294_);
if (v___x_5295_ == 0)
{
size_t v___x_5296_; size_t v___x_5297_; 
v___x_5296_ = ((size_t)1ULL);
v___x_5297_ = lean_usize_add(v_i_5291_, v___x_5296_);
v_i_5291_ = v___x_5297_;
goto _start;
}
else
{
return v___x_5295_;
}
}
else
{
uint8_t v___x_5299_; 
v___x_5299_ = 0;
return v___x_5299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5300_, lean_object* v_as_5301_, lean_object* v_i_5302_, lean_object* v_stop_5303_){
_start:
{
size_t v_i_boxed_5304_; size_t v_stop_boxed_5305_; uint8_t v_res_5306_; lean_object* v_r_5307_; 
v_i_boxed_5304_ = lean_unbox_usize(v_i_5302_);
lean_dec(v_i_5302_);
v_stop_boxed_5305_ = lean_unbox_usize(v_stop_5303_);
lean_dec(v_stop_5303_);
v_res_5306_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5300_, v_as_5301_, v_i_boxed_5304_, v_stop_boxed_5305_);
lean_dec_ref(v_as_5301_);
lean_dec_ref(v_a_5300_);
v_r_5307_ = lean_box(v_res_5306_);
return v_r_5307_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v___x_5310_; lean_object* v___x_5311_; uint8_t v___x_5312_; 
v___x_5310_ = lean_unsigned_to_nat(0u);
v___x_5311_ = lean_array_get_size(v_as_5308_);
v___x_5312_ = lean_nat_dec_lt(v___x_5310_, v___x_5311_);
if (v___x_5312_ == 0)
{
return v___x_5312_;
}
else
{
if (v___x_5312_ == 0)
{
return v___x_5312_;
}
else
{
size_t v___x_5313_; size_t v___x_5314_; uint8_t v___x_5315_; 
v___x_5313_ = ((size_t)0ULL);
v___x_5314_ = lean_usize_of_nat(v___x_5311_);
v___x_5315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5309_, v_as_5308_, v___x_5313_, v___x_5314_);
return v___x_5315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5316_, lean_object* v_a_5317_){
_start:
{
uint8_t v_res_5318_; lean_object* v_r_5319_; 
v_res_5318_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5316_, v_a_5317_);
lean_dec_ref(v_a_5317_);
lean_dec_ref(v_as_5316_);
v_r_5319_ = lean_box(v_res_5318_);
return v_r_5319_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5320_, lean_object* v_e_5321_){
_start:
{
uint8_t v___x_5322_; lean_object* v_d_5324_; lean_object* v_b_5325_; 
v___x_5322_ = l_Lean_Expr_hasFVar(v_e_5321_);
if (v___x_5322_ == 0)
{
lean_dec_ref(v_e_5321_);
return v___x_5322_;
}
else
{
switch(lean_obj_tag(v_e_5321_))
{
case 7:
{
lean_object* v_binderType_5328_; lean_object* v_body_5329_; 
v_binderType_5328_ = lean_ctor_get(v_e_5321_, 1);
lean_inc_ref(v_binderType_5328_);
v_body_5329_ = lean_ctor_get(v_e_5321_, 2);
lean_inc_ref(v_body_5329_);
lean_dec_ref_known(v_e_5321_, 3);
v_d_5324_ = v_binderType_5328_;
v_b_5325_ = v_body_5329_;
goto v___jp_5323_;
}
case 6:
{
lean_object* v_binderType_5330_; lean_object* v_body_5331_; 
v_binderType_5330_ = lean_ctor_get(v_e_5321_, 1);
lean_inc_ref(v_binderType_5330_);
v_body_5331_ = lean_ctor_get(v_e_5321_, 2);
lean_inc_ref(v_body_5331_);
lean_dec_ref_known(v_e_5321_, 3);
v_d_5324_ = v_binderType_5330_;
v_b_5325_ = v_body_5331_;
goto v___jp_5323_;
}
case 10:
{
lean_object* v_expr_5332_; 
v_expr_5332_ = lean_ctor_get(v_e_5321_, 1);
lean_inc_ref(v_expr_5332_);
lean_dec_ref_known(v_e_5321_, 2);
v_e_5321_ = v_expr_5332_;
goto _start;
}
case 8:
{
lean_object* v_type_5334_; lean_object* v_value_5335_; lean_object* v_body_5336_; uint8_t v___x_5337_; 
v_type_5334_ = lean_ctor_get(v_e_5321_, 1);
lean_inc_ref(v_type_5334_);
v_value_5335_ = lean_ctor_get(v_e_5321_, 2);
lean_inc_ref(v_value_5335_);
v_body_5336_ = lean_ctor_get(v_e_5321_, 3);
lean_inc_ref(v_body_5336_);
lean_dec_ref_known(v_e_5321_, 4);
v___x_5337_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5320_, v_type_5334_);
if (v___x_5337_ == 0)
{
uint8_t v___x_5338_; 
v___x_5338_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5320_, v_value_5335_);
if (v___x_5338_ == 0)
{
v_e_5321_ = v_body_5336_;
goto _start;
}
else
{
lean_dec_ref(v_body_5336_);
return v___x_5322_;
}
}
else
{
lean_dec_ref(v_body_5336_);
lean_dec_ref(v_value_5335_);
return v___x_5322_;
}
}
case 5:
{
lean_object* v_fn_5340_; lean_object* v_arg_5341_; uint8_t v___x_5342_; 
v_fn_5340_ = lean_ctor_get(v_e_5321_, 0);
lean_inc_ref(v_fn_5340_);
v_arg_5341_ = lean_ctor_get(v_e_5321_, 1);
lean_inc_ref(v_arg_5341_);
lean_dec_ref_known(v_e_5321_, 2);
v___x_5342_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5320_, v_fn_5340_);
if (v___x_5342_ == 0)
{
v_e_5321_ = v_arg_5341_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5341_);
return v___x_5322_;
}
}
case 11:
{
lean_object* v_struct_5344_; 
v_struct_5344_ = lean_ctor_get(v_e_5321_, 2);
lean_inc_ref(v_struct_5344_);
lean_dec_ref_known(v_e_5321_, 3);
v_e_5321_ = v_struct_5344_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5346_; lean_object* v___x_5347_; uint8_t v___x_5348_; 
v_fvarId_5346_ = lean_ctor_get(v_e_5321_, 0);
lean_inc(v_fvarId_5346_);
lean_dec_ref_known(v_e_5321_, 1);
v___x_5347_ = l_Lean_Expr_fvar___override(v_fvarId_5346_);
v___x_5348_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5320_, v___x_5347_);
lean_dec_ref(v___x_5347_);
return v___x_5348_;
}
default: 
{
uint8_t v___x_5349_; 
lean_dec_ref(v_e_5321_);
v___x_5349_ = 0;
return v___x_5349_;
}
}
}
v___jp_5323_:
{
uint8_t v___x_5326_; 
v___x_5326_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5320_, v_d_5324_);
if (v___x_5326_ == 0)
{
v_e_5321_ = v_b_5325_;
goto _start;
}
else
{
lean_dec_ref(v_b_5325_);
return v___x_5322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5350_, lean_object* v_e_5351_){
_start:
{
uint8_t v_res_5352_; lean_object* v_r_5353_; 
v_res_5352_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5350_, v_e_5351_);
lean_dec_ref(v_xs_5350_);
v_r_5353_ = lean_box(v_res_5352_);
return v_r_5353_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5356_ = l_Lean_stringToMessageData(v___x_5355_);
return v___x_5356_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5359_ = l_Lean_stringToMessageData(v___x_5358_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5360_, lean_object* v_type_5361_, lean_object* v_as_5362_, size_t v_sz_5363_, size_t v_i_5364_, lean_object* v_b_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v_a_5372_; uint8_t v___x_5376_; 
v___x_5376_ = lean_usize_dec_lt(v_i_5364_, v_sz_5363_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5377_; 
lean_dec_ref(v_type_5361_);
v___x_5377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5377_, 0, v_b_5365_);
return v___x_5377_;
}
else
{
lean_object* v___x_5378_; lean_object* v_a_5379_; uint8_t v___x_5380_; 
v___x_5378_ = lean_box(0);
v_a_5379_ = lean_array_uget_borrowed(v_as_5362_, v_i_5364_);
lean_inc(v_a_5379_);
v___x_5380_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5360_, v_a_5379_);
if (v___x_5380_ == 0)
{
v_a_5372_ = v___x_5378_;
goto v___jp_5371_;
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5381_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5379_);
v___x_5382_ = l_Lean_MessageData_ofExpr(v_a_5379_);
v___x_5383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5381_);
lean_ctor_set(v___x_5383_, 1, v___x_5382_);
v___x_5384_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5383_);
lean_ctor_set(v___x_5385_, 1, v___x_5384_);
lean_inc_ref(v_type_5361_);
v___x_5386_ = l_Lean_MessageData_ofExpr(v_type_5361_);
v___x_5387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5385_);
lean_ctor_set(v___x_5387_, 1, v___x_5386_);
v___x_5388_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5387_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_);
if (lean_obj_tag(v___x_5388_) == 0)
{
lean_dec_ref_known(v___x_5388_, 1);
v_a_5372_ = v___x_5378_;
goto v___jp_5371_;
}
else
{
lean_dec_ref(v_type_5361_);
return v___x_5388_;
}
}
}
v___jp_5371_:
{
size_t v___x_5373_; size_t v___x_5374_; 
v___x_5373_ = ((size_t)1ULL);
v___x_5374_ = lean_usize_add(v_i_5364_, v___x_5373_);
v_i_5364_ = v___x_5374_;
v_b_5365_ = v_a_5372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5389_, lean_object* v_type_5390_, lean_object* v_as_5391_, lean_object* v_sz_5392_, lean_object* v_i_5393_, lean_object* v_b_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
size_t v_sz_boxed_5400_; size_t v_i_boxed_5401_; lean_object* v_res_5402_; 
v_sz_boxed_5400_ = lean_unbox_usize(v_sz_5392_);
lean_dec(v_sz_5392_);
v_i_boxed_5401_ = lean_unbox_usize(v_i_5393_);
lean_dec(v_i_5393_);
v_res_5402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5389_, v_type_5390_, v_as_5391_, v_sz_boxed_5400_, v_i_boxed_5401_, v_b_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
lean_dec(v___y_5396_);
lean_dec_ref(v___y_5395_);
lean_dec_ref(v_as_5391_);
lean_dec_ref(v_xs_5389_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5403_, size_t v_i_5404_, lean_object* v_bs_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
uint8_t v___x_5411_; 
v___x_5411_ = lean_usize_dec_lt(v_i_5404_, v_sz_5403_);
if (v___x_5411_ == 0)
{
lean_object* v___x_5412_; 
v___x_5412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5412_, 0, v_bs_5405_);
return v___x_5412_;
}
else
{
lean_object* v_v_5413_; lean_object* v___x_5414_; 
v_v_5413_ = lean_array_uget_borrowed(v_bs_5405_, v_i_5404_);
lean_inc(v___y_5409_);
lean_inc_ref(v___y_5408_);
lean_inc(v___y_5407_);
lean_inc_ref(v___y_5406_);
lean_inc(v_v_5413_);
v___x_5414_ = lean_infer_type(v_v_5413_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v_a_5415_; lean_object* v___x_5416_; lean_object* v_bs_x27_5417_; size_t v___x_5418_; size_t v___x_5419_; lean_object* v___x_5420_; 
v_a_5415_ = lean_ctor_get(v___x_5414_, 0);
lean_inc(v_a_5415_);
lean_dec_ref_known(v___x_5414_, 1);
v___x_5416_ = lean_unsigned_to_nat(0u);
v_bs_x27_5417_ = lean_array_uset(v_bs_5405_, v_i_5404_, v___x_5416_);
v___x_5418_ = ((size_t)1ULL);
v___x_5419_ = lean_usize_add(v_i_5404_, v___x_5418_);
v___x_5420_ = lean_array_uset(v_bs_x27_5417_, v_i_5404_, v_a_5415_);
v_i_5404_ = v___x_5419_;
v_bs_5405_ = v___x_5420_;
goto _start;
}
else
{
lean_object* v_a_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5429_; 
lean_dec_ref(v_bs_5405_);
v_a_5422_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5429_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5429_ == 0)
{
v___x_5424_ = v___x_5414_;
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_a_5422_);
lean_dec(v___x_5414_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5427_; 
if (v_isShared_5425_ == 0)
{
v___x_5427_ = v___x_5424_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_a_5422_);
v___x_5427_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
return v___x_5427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5430_, lean_object* v_i_5431_, lean_object* v_bs_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
size_t v_sz_boxed_5438_; size_t v_i_boxed_5439_; lean_object* v_res_5440_; 
v_sz_boxed_5438_ = lean_unbox_usize(v_sz_5430_);
lean_dec(v_sz_5430_);
v_i_boxed_5439_ = lean_unbox_usize(v_i_5431_);
lean_dec(v_i_5431_);
v_res_5440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5438_, v_i_boxed_5439_, v_bs_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
return v_res_5440_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5443_ = l_Lean_stringToMessageData(v___x_5442_);
return v___x_5443_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5445_; lean_object* v___x_5446_; 
v___x_5445_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5446_ = l_Lean_stringToMessageData(v___x_5445_);
return v___x_5446_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5448_; lean_object* v___x_5449_; 
v___x_5448_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5449_ = l_Lean_stringToMessageData(v___x_5448_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5450_, lean_object* v_n_5451_, lean_object* v_xs_5452_, lean_object* v_x_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v___x_5483_; uint8_t v___x_5484_; 
v___x_5483_ = lean_array_get_size(v_xs_5452_);
v___x_5484_ = lean_nat_dec_eq(v___x_5483_, v_n_5451_);
if (v___x_5484_ == 0)
{
lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5504_; 
lean_dec_ref(v_xs_5452_);
v___x_5485_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5486_ = l_Lean_MessageData_ofExpr(v_type_5450_);
v___x_5487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5487_, 0, v___x_5485_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
v___x_5488_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5487_);
lean_ctor_set(v___x_5489_, 1, v___x_5488_);
v___x_5490_ = l_Nat_reprFast(v_n_5451_);
v___x_5491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5491_, 0, v___x_5490_);
v___x_5492_ = l_Lean_MessageData_ofFormat(v___x_5491_);
v___x_5493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5493_, 0, v___x_5489_);
lean_ctor_set(v___x_5493_, 1, v___x_5492_);
v___x_5494_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5493_);
lean_ctor_set(v___x_5495_, 1, v___x_5494_);
v___x_5496_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5495_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5499_ = v___x_5496_;
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v___x_5496_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5502_; 
if (v_isShared_5500_ == 0)
{
v___x_5502_ = v___x_5499_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_a_5497_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
else
{
lean_dec(v_n_5451_);
goto v___jp_5459_;
}
v___jp_5459_:
{
size_t v_sz_5460_; size_t v___x_5461_; lean_object* v___x_5462_; 
v_sz_5460_ = lean_array_size(v_xs_5452_);
v___x_5461_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5452_);
v___x_5462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5460_, v___x_5461_, v_xs_5452_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
if (lean_obj_tag(v___x_5462_) == 0)
{
lean_object* v_a_5463_; lean_object* v___x_5464_; size_t v_sz_5465_; lean_object* v___x_5466_; 
v_a_5463_ = lean_ctor_get(v___x_5462_, 0);
lean_inc(v_a_5463_);
lean_dec_ref_known(v___x_5462_, 1);
v___x_5464_ = lean_box(0);
v_sz_5465_ = lean_array_size(v_a_5463_);
v___x_5466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5452_, v_type_5450_, v_a_5463_, v_sz_5465_, v___x_5461_, v___x_5464_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
lean_dec_ref(v_xs_5452_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5473_; 
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5473_ == 0)
{
lean_object* v_unused_5474_; 
v_unused_5474_ = lean_ctor_get(v___x_5466_, 0);
lean_dec(v_unused_5474_);
v___x_5468_ = v___x_5466_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_dec(v___x_5466_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5471_; 
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v_a_5463_);
v___x_5471_ = v___x_5468_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5463_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_dec(v_a_5463_);
v_a_5475_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5466_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5466_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5452_);
lean_dec_ref(v_type_5450_);
return v___x_5462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5505_, lean_object* v_n_5506_, lean_object* v_xs_5507_, lean_object* v_x_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_){
_start:
{
lean_object* v_res_5514_; 
v_res_5514_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5505_, v_n_5506_, v_xs_5507_, v_x_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec_ref(v_x_5508_);
return v_res_5514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5515_, lean_object* v_type_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_){
_start:
{
lean_object* v___f_5522_; lean_object* v___x_5523_; uint8_t v___x_5524_; lean_object* v___x_5525_; 
lean_inc(v_n_5515_);
lean_inc_ref(v_type_5516_);
v___f_5522_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5522_, 0, v_type_5516_);
lean_closure_set(v___f_5522_, 1, v_n_5515_);
v___x_5523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5523_, 0, v_n_5515_);
v___x_5524_ = 0;
v___x_5525_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5516_, v___x_5523_, v___f_5522_, v___x_5524_, v___x_5524_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_);
return v___x_5525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5526_, lean_object* v_type_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_){
_start:
{
lean_object* v_res_5533_; 
v_res_5533_ = l_Lean_Meta_arrowDomainsN(v_n_5526_, v_type_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
lean_dec(v_a_5531_);
lean_dec_ref(v_a_5530_);
lean_dec(v_a_5529_);
lean_dec_ref(v_a_5528_);
return v_res_5533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5534_, lean_object* v_e_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_){
_start:
{
lean_object* v___x_5541_; 
lean_inc(v_a_5539_);
lean_inc_ref(v_a_5538_);
lean_inc(v_a_5537_);
lean_inc_ref(v_a_5536_);
v___x_5541_ = lean_infer_type(v_e_5535_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_a_5542_; lean_object* v___x_5543_; 
v_a_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_a_5542_);
lean_dec_ref_known(v___x_5541_, 1);
v___x_5543_ = l_Lean_Meta_arrowDomainsN(v_n_5534_, v_a_5542_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_);
return v___x_5543_;
}
else
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5551_; 
lean_dec(v_n_5534_);
v_a_5544_ = lean_ctor_get(v___x_5541_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5546_ = v___x_5541_;
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5541_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5547_ == 0)
{
v___x_5549_ = v___x_5546_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5552_, lean_object* v_e_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_){
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l_Lean_Meta_inferArgumentTypesN(v_n_5552_, v_e_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_);
lean_dec(v_a_5557_);
lean_dec_ref(v_a_5556_);
lean_dec(v_a_5555_);
lean_dec_ref(v_a_5554_);
return v_res_5559_;
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
