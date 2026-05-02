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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Bool_toLBool(uint8_t);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2;
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
static lean_object* _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___f_3_; 
v___x_2_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_3_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3_, 0, v___x_2_);
return v___f_3_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(lean_object* v_msg_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___f_16_; lean_object* v___f_17_; lean_object* v___x_18_; lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_4201__overap_34_; lean_object* v___x_35_; 
v___x_15_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0));
v___f_16_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1, &l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_once, _init_l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1);
v___f_17_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_17_, 0, v___x_15_);
lean_closure_set(v___f_17_, 1, v___f_16_);
v___x_18_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2));
v___f_19_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3));
v___f_20_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_20_, 0, v___x_18_);
lean_closure_set(v___f_20_, 1, v___f_19_);
v___f_21_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4));
v___f_22_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5));
v___f_23_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6));
v___f_24_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__7));
v___f_25_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__8));
v___f_26_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__9));
v___f_27_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__10));
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___f_21_);
lean_ctor_set(v___x_28_, 1, v___f_22_);
v___x_29_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___f_23_);
lean_ctor_set(v___x_29_, 2, v___f_24_);
lean_ctor_set(v___x_29_, 3, v___f_25_);
lean_ctor_set(v___x_29_, 4, v___f_26_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___f_27_);
v___x_31_ = l_Lean_MonadStateCacheT_instMonad___redArg(v___f_17_, v___f_20_, v___x_30_);
v___x_32_ = l_Lean_instInhabitedExpr;
v___x_33_ = l_instInhabitedOfMonad___redArg(v___x_31_, v___x_32_);
v___x_4201__overap_34_ = lean_panic_fn_borrowed(v___x_33_, v_msg_13_);
lean_dec(v___x_33_);
v___x_35_ = lean_apply_1(v___x_4201__overap_34_, v___y_14_);
return v___x_35_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(lean_object* v_a_36_, lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
uint8_t v___x_38_; 
v___x_38_ = 0;
return v___x_38_;
}
else
{
lean_object* v_key_39_; lean_object* v_tail_40_; uint8_t v___y_42_; lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; uint8_t v___x_48_; 
v_key_39_ = lean_ctor_get(v_x_37_, 0);
v_tail_40_ = lean_ctor_get(v_x_37_, 2);
v_fst_44_ = lean_ctor_get(v_key_39_, 0);
v_snd_45_ = lean_ctor_get(v_key_39_, 1);
v_fst_46_ = lean_ctor_get(v_a_36_, 0);
v_snd_47_ = lean_ctor_get(v_a_36_, 1);
v___x_48_ = l_Lean_ExprStructEq_beq(v_fst_44_, v_fst_46_);
if (v___x_48_ == 0)
{
v___y_42_ = v___x_48_;
goto v___jp_41_;
}
else
{
uint8_t v___x_49_; 
v___x_49_ = lean_nat_dec_eq(v_snd_45_, v_snd_47_);
v___y_42_ = v___x_49_;
goto v___jp_41_;
}
v___jp_41_:
{
if (v___y_42_ == 0)
{
v_x_37_ = v_tail_40_;
goto _start;
}
else
{
return v___y_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_50_, lean_object* v_x_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(v_a_50_, v_x_51_);
lean_dec(v_x_51_);
lean_dec_ref(v_a_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
return v_x_54_;
}
else
{
lean_object* v_key_56_; lean_object* v_value_57_; lean_object* v_tail_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_85_; 
v_key_56_ = lean_ctor_get(v_x_55_, 0);
v_value_57_ = lean_ctor_get(v_x_55_, 1);
v_tail_58_ = lean_ctor_get(v_x_55_, 2);
v_isSharedCheck_85_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_85_ == 0)
{
v___x_60_ = v_x_55_;
v_isShared_61_ = v_isSharedCheck_85_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_tail_58_);
lean_inc(v_value_57_);
lean_inc(v_key_56_);
lean_dec(v_x_55_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_85_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_64_; uint64_t v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v_fold_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v_fst_62_ = lean_ctor_get(v_key_56_, 0);
v_snd_63_ = lean_ctor_get(v_key_56_, 1);
v___x_64_ = lean_array_get_size(v_x_54_);
v___x_65_ = l_Lean_ExprStructEq_hash(v_fst_62_);
v___x_66_ = lean_uint64_of_nat(v_snd_63_);
v___x_67_ = lean_uint64_mix_hash(v___x_65_, v___x_66_);
v___x_68_ = 32ULL;
v___x_69_ = lean_uint64_shift_right(v___x_67_, v___x_68_);
v_fold_70_ = lean_uint64_xor(v___x_67_, v___x_69_);
v___x_71_ = 16ULL;
v___x_72_ = lean_uint64_shift_right(v_fold_70_, v___x_71_);
v___x_73_ = lean_uint64_xor(v_fold_70_, v___x_72_);
v___x_74_ = lean_uint64_to_usize(v___x_73_);
v___x_75_ = lean_usize_of_nat(v___x_64_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_sub(v___x_75_, v___x_76_);
v___x_78_ = lean_usize_land(v___x_74_, v___x_77_);
v___x_79_ = lean_array_uget_borrowed(v_x_54_, v___x_78_);
lean_inc(v___x_79_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 2, v___x_79_);
v___x_81_ = v___x_60_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_key_56_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_value_57_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v___x_79_);
v___x_81_ = v_reuseFailAlloc_84_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; 
v___x_82_ = lean_array_uset(v_x_54_, v___x_78_, v___x_81_);
v_x_54_ = v___x_82_;
v_x_55_ = v_tail_58_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4___redArg(lean_object* v_i_86_, lean_object* v_source_87_, lean_object* v_target_88_){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_array_get_size(v_source_87_);
v___x_90_ = lean_nat_dec_lt(v_i_86_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec_ref(v_source_87_);
lean_dec(v_i_86_);
return v_target_88_;
}
else
{
lean_object* v_es_91_; lean_object* v___x_92_; lean_object* v_source_93_; lean_object* v_target_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_es_91_ = lean_array_fget(v_source_87_, v_i_86_);
v___x_92_ = lean_box(0);
v_source_93_ = lean_array_fset(v_source_87_, v_i_86_, v___x_92_);
v_target_94_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7___redArg(v_target_88_, v_es_91_);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_add(v_i_86_, v___x_95_);
lean_dec(v_i_86_);
v_i_86_ = v___x_96_;
v_source_87_ = v_source_93_;
v_target_88_ = v_target_94_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2___redArg(lean_object* v_data_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_nbuckets_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_99_ = lean_array_get_size(v_data_98_);
v___x_100_ = lean_unsigned_to_nat(2u);
v_nbuckets_101_ = lean_nat_mul(v___x_99_, v___x_100_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_box(0);
v___x_104_ = lean_mk_array(v_nbuckets_101_, v___x_103_);
v___x_105_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4___redArg(v___x_102_, v_data_98_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(lean_object* v_a_106_, lean_object* v_b_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_dec(v_b_107_);
lean_dec_ref(v_a_106_);
return v_x_108_;
}
else
{
lean_object* v_key_109_; lean_object* v_value_110_; lean_object* v_tail_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_130_; 
v_key_109_ = lean_ctor_get(v_x_108_, 0);
v_value_110_ = lean_ctor_get(v_x_108_, 1);
v_tail_111_ = lean_ctor_get(v_x_108_, 2);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_130_ == 0)
{
v___x_113_ = v_x_108_;
v_isShared_114_ = v_isSharedCheck_130_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_tail_111_);
lean_inc(v_value_110_);
lean_inc(v_key_109_);
lean_dec(v_x_108_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_130_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___y_116_; lean_object* v_fst_124_; lean_object* v_snd_125_; lean_object* v_fst_126_; lean_object* v_snd_127_; uint8_t v___x_128_; 
v_fst_124_ = lean_ctor_get(v_key_109_, 0);
v_snd_125_ = lean_ctor_get(v_key_109_, 1);
v_fst_126_ = lean_ctor_get(v_a_106_, 0);
v_snd_127_ = lean_ctor_get(v_a_106_, 1);
v___x_128_ = l_Lean_ExprStructEq_beq(v_fst_124_, v_fst_126_);
if (v___x_128_ == 0)
{
v___y_116_ = v___x_128_;
goto v___jp_115_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_eq(v_snd_125_, v_snd_127_);
v___y_116_ = v___x_129_;
goto v___jp_115_;
}
v___jp_115_:
{
if (v___y_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(v_a_106_, v_b_107_, v_tail_111_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 2, v___x_117_);
v___x_119_ = v___x_113_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_key_109_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_value_110_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
else
{
lean_object* v___x_122_; 
lean_dec(v_value_110_);
lean_dec(v_key_109_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_b_107_);
lean_ctor_set(v___x_113_, 0, v_a_106_);
v___x_122_ = v___x_113_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_106_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_b_107_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_tail_111_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(lean_object* v_m_131_, lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
lean_object* v_size_134_; lean_object* v_buckets_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_182_; 
v_size_134_ = lean_ctor_get(v_m_131_, 0);
v_buckets_135_ = lean_ctor_get(v_m_131_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_m_131_);
if (v_isSharedCheck_182_ == 0)
{
v___x_137_ = v_m_131_;
v_isShared_138_ = v_isSharedCheck_182_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_buckets_135_);
lean_inc(v_size_134_);
lean_dec(v_m_131_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_182_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v_fold_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; lean_object* v_bkt_156_; uint8_t v___x_157_; 
v_fst_139_ = lean_ctor_get(v_a_132_, 0);
v_snd_140_ = lean_ctor_get(v_a_132_, 1);
v___x_141_ = lean_array_get_size(v_buckets_135_);
v___x_142_ = l_Lean_ExprStructEq_hash(v_fst_139_);
v___x_143_ = lean_uint64_of_nat(v_snd_140_);
v___x_144_ = lean_uint64_mix_hash(v___x_142_, v___x_143_);
v___x_145_ = 32ULL;
v___x_146_ = lean_uint64_shift_right(v___x_144_, v___x_145_);
v_fold_147_ = lean_uint64_xor(v___x_144_, v___x_146_);
v___x_148_ = 16ULL;
v___x_149_ = lean_uint64_shift_right(v_fold_147_, v___x_148_);
v___x_150_ = lean_uint64_xor(v_fold_147_, v___x_149_);
v___x_151_ = lean_uint64_to_usize(v___x_150_);
v___x_152_ = lean_usize_of_nat(v___x_141_);
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_sub(v___x_152_, v___x_153_);
v___x_155_ = lean_usize_land(v___x_151_, v___x_154_);
v_bkt_156_ = lean_array_uget_borrowed(v_buckets_135_, v___x_155_);
v___x_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(v_a_132_, v_bkt_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v_size_x27_159_; lean_object* v___x_160_; lean_object* v_buckets_x27_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v_size_x27_159_ = lean_nat_add(v_size_134_, v___x_158_);
lean_dec(v_size_134_);
lean_inc(v_bkt_156_);
v___x_160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_160_, 0, v_a_132_);
lean_ctor_set(v___x_160_, 1, v_b_133_);
lean_ctor_set(v___x_160_, 2, v_bkt_156_);
v_buckets_x27_161_ = lean_array_uset(v_buckets_135_, v___x_155_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_mul(v_size_x27_159_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(3u);
v___x_165_ = lean_nat_div(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_array_get_size(v_buckets_x27_161_);
v___x_167_ = lean_nat_dec_le(v___x_165_, v___x_166_);
lean_dec(v___x_165_);
if (v___x_167_ == 0)
{
lean_object* v_val_168_; lean_object* v___x_170_; 
v_val_168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2___redArg(v_buckets_x27_161_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v_val_168_);
lean_ctor_set(v___x_137_, 0, v_size_x27_159_);
v___x_170_ = v___x_137_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_x27_159_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_val_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v___x_173_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v_buckets_x27_161_);
lean_ctor_set(v___x_137_, 0, v_size_x27_159_);
v___x_173_ = v___x_137_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_size_x27_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_buckets_x27_161_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
else
{
lean_object* v___x_175_; lean_object* v_buckets_x27_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_inc(v_bkt_156_);
v___x_175_ = lean_box(0);
v_buckets_x27_176_ = lean_array_uset(v_buckets_135_, v___x_155_, v___x_175_);
v___x_177_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(v_a_132_, v_b_133_, v_bkt_156_);
v___x_178_ = lean_array_uset(v_buckets_x27_176_, v___x_155_, v___x_177_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_178_);
v___x_180_ = v___x_137_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_size_134_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(lean_object* v_a_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v_key_186_; lean_object* v_value_187_; lean_object* v_tail_188_; uint8_t v___y_190_; lean_object* v_fst_193_; lean_object* v_snd_194_; lean_object* v_fst_195_; lean_object* v_snd_196_; uint8_t v___x_197_; 
v_key_186_ = lean_ctor_get(v_x_184_, 0);
v_value_187_ = lean_ctor_get(v_x_184_, 1);
v_tail_188_ = lean_ctor_get(v_x_184_, 2);
v_fst_193_ = lean_ctor_get(v_key_186_, 0);
v_snd_194_ = lean_ctor_get(v_key_186_, 1);
v_fst_195_ = lean_ctor_get(v_a_183_, 0);
v_snd_196_ = lean_ctor_get(v_a_183_, 1);
v___x_197_ = l_Lean_ExprStructEq_beq(v_fst_193_, v_fst_195_);
if (v___x_197_ == 0)
{
v___y_190_ = v___x_197_;
goto v___jp_189_;
}
else
{
uint8_t v___x_198_; 
v___x_198_ = lean_nat_dec_eq(v_snd_194_, v_snd_196_);
v___y_190_ = v___x_198_;
goto v___jp_189_;
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
v_x_184_ = v_tail_188_;
goto _start;
}
else
{
lean_object* v___x_192_; 
lean_inc(v_value_187_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_value_187_);
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg___boxed(lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(v_a_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec_ref(v_a_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(lean_object* v_m_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_buckets_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; lean_object* v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v_fold_213_; uint64_t v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_buckets_204_ = lean_ctor_get(v_m_202_, 1);
v_fst_205_ = lean_ctor_get(v_a_203_, 0);
v_snd_206_ = lean_ctor_get(v_a_203_, 1);
v___x_207_ = lean_array_get_size(v_buckets_204_);
v___x_208_ = l_Lean_ExprStructEq_hash(v_fst_205_);
v___x_209_ = lean_uint64_of_nat(v_snd_206_);
v___x_210_ = lean_uint64_mix_hash(v___x_208_, v___x_209_);
v___x_211_ = 32ULL;
v___x_212_ = lean_uint64_shift_right(v___x_210_, v___x_211_);
v_fold_213_ = lean_uint64_xor(v___x_210_, v___x_212_);
v___x_214_ = 16ULL;
v___x_215_ = lean_uint64_shift_right(v_fold_213_, v___x_214_);
v___x_216_ = lean_uint64_xor(v_fold_213_, v___x_215_);
v___x_217_ = lean_uint64_to_usize(v___x_216_);
v___x_218_ = lean_usize_of_nat(v___x_207_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_sub(v___x_218_, v___x_219_);
v___x_221_ = lean_usize_land(v___x_217_, v___x_220_);
v___x_222_ = lean_array_uget_borrowed(v_buckets_204_, v___x_221_);
v___x_223_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(v_a_203_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg___boxed(lean_object* v_m_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(v_m_224_, v_a_225_);
lean_dec_ref(v_a_225_);
lean_dec_ref(v_m_224_);
return v_res_226_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_231_ = lean_unsigned_to_nat(21u);
v___x_232_ = lean_unsigned_to_nat(69u);
v___x_233_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_235_ = l_mkPanicMessageWithDecl(v___x_234_, v___x_233_, v___x_232_, v___x_231_, v___x_230_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_236_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_237_ = lean_unsigned_to_nat(21u);
v___x_238_ = lean_unsigned_to_nat(70u);
v___x_239_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_241_ = l_mkPanicMessageWithDecl(v___x_240_, v___x_239_, v___x_238_, v___x_237_, v___x_236_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_243_ = lean_unsigned_to_nat(21u);
v___x_244_ = lean_unsigned_to_nat(71u);
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_247_ = l_mkPanicMessageWithDecl(v___x_246_, v___x_245_, v___x_244_, v___x_243_, v___x_242_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_249_ = lean_unsigned_to_nat(21u);
v___x_250_ = lean_unsigned_to_nat(68u);
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_252_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_253_ = l_mkPanicMessageWithDecl(v___x_252_, v___x_251_, v___x_250_, v___x_249_, v___x_248_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_start_254_, lean_object* v_stop_255_, lean_object* v_args_256_, lean_object* v_offset_257_, lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v___y_260_){
_start:
{
if (lean_obj_tag(v_x_258_) == 5)
{
lean_object* v_fn_261_; lean_object* v_arg_262_; lean_object* v___x_263_; 
v_fn_261_ = lean_ctor_get(v_x_258_, 0);
lean_inc_ref(v_fn_261_);
v_arg_262_ = lean_ctor_get(v_x_258_, 1);
lean_inc_ref(v_arg_262_);
lean_dec_ref(v_x_258_);
v___x_263_ = lean_array_push(v_x_259_, v_arg_262_);
v_x_258_ = v_fn_261_;
v_x_259_ = v___x_263_;
goto _start;
}
else
{
lean_object* v___x_265_; lean_object* v_fst_266_; lean_object* v_snd_267_; size_t v_sz_268_; size_t v___x_269_; lean_object* v___x_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_286_; 
lean_inc(v_offset_257_);
lean_inc_ref(v_x_258_);
v___x_265_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_254_, v_stop_255_, v_args_256_, v_x_258_, v_offset_257_, v___y_260_);
v_fst_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_fst_266_);
v_snd_267_ = lean_ctor_get(v___x_265_, 1);
lean_inc(v_snd_267_);
lean_dec_ref(v___x_265_);
v_sz_268_ = lean_array_size(v_x_259_);
v___x_269_ = ((size_t)0ULL);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0(v_start_254_, v_stop_255_, v_args_256_, v_offset_257_, v_sz_268_, v___x_269_, v_x_259_, v_snd_267_);
v_fst_271_ = lean_ctor_get(v___x_270_, 0);
v_snd_272_ = lean_ctor_get(v___x_270_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_286_ == 0)
{
v___x_274_ = v___x_270_;
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_snd_272_);
lean_inc(v_fst_271_);
lean_dec(v___x_270_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
uint8_t v___x_276_; 
v___x_276_ = l_Lean_Expr_isBVar(v_x_258_);
lean_dec_ref(v_x_258_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = l_Lean_mkAppRev(v_fst_266_, v_fst_271_);
lean_dec(v_fst_271_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_277_);
v___x_279_ = v___x_274_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_snd_272_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
else
{
uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_281_ = 0;
v___x_282_ = l_Lean_Expr_betaRev(v_fst_266_, v_fst_271_, v___x_281_, v___x_281_);
lean_dec(v_fst_271_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_282_);
v___x_284_ = v___x_274_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_snd_272_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_288_ = lean_unsigned_to_nat(21u);
v___x_289_ = lean_unsigned_to_nat(72u);
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_292_ = l_mkPanicMessageWithDecl(v___x_291_, v___x_290_, v___x_289_, v___x_288_, v___x_287_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object* v_start_293_, lean_object* v_stop_294_, lean_object* v_args_295_, lean_object* v_e_296_, lean_object* v_offset_297_, lean_object* v_a_298_){
_start:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = l_Lean_Expr_looseBVarRange(v_e_296_);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_offset_297_);
lean_dec(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v_fst_303_; lean_object* v_snd_304_; lean_object* v___y_308_; lean_object* v___x_311_; 
lean_inc(v_offset_297_);
lean_inc_ref(v_e_296_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_e_296_);
lean_ctor_set(v___x_301_, 1, v_offset_297_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(v_a_298_, v___x_301_);
if (lean_obj_tag(v___x_311_) == 0)
{
switch(lean_obj_tag(v_e_296_))
{
case 0:
{
lean_object* v_deBruijnIndex_312_; lean_object* v_n_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_deBruijnIndex_312_ = lean_ctor_get(v_e_296_, 0);
lean_inc(v_deBruijnIndex_312_);
lean_dec_ref(v_e_296_);
v_n_313_ = lean_nat_sub(v_stop_294_, v_start_293_);
v___x_314_ = lean_nat_add(v_offset_297_, v_n_313_);
v___x_315_ = lean_nat_dec_lt(v_deBruijnIndex_312_, v___x_314_);
lean_dec(v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_offset_297_);
v___x_316_ = lean_nat_sub(v_deBruijnIndex_312_, v_n_313_);
lean_dec(v_n_313_);
lean_dec(v_deBruijnIndex_312_);
v___x_317_ = l_Lean_mkBVar(v___x_316_);
v_fst_303_ = v___x_317_;
v_snd_304_ = v_a_298_;
goto v___jp_302_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_n_313_);
v___x_318_ = l_Lean_instInhabitedExpr;
v___x_319_ = lean_nat_sub(v_deBruijnIndex_312_, v_offset_297_);
lean_dec(v_deBruijnIndex_312_);
v___x_320_ = lean_nat_sub(v_stop_294_, v___x_319_);
lean_dec(v___x_319_);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_sub(v___x_320_, v___x_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_array_get_borrowed(v___x_318_, v_args_295_, v___x_322_);
lean_dec(v___x_322_);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_expr_lift_loose_bvars(v___x_323_, v___x_324_, v_offset_297_);
lean_dec(v_offset_297_);
v_fst_303_ = v___x_325_;
v_snd_304_ = v_a_298_;
goto v___jp_302_;
}
}
case 1:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec_ref(v_e_296_);
lean_dec(v_offset_297_);
v___x_326_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3);
v___x_327_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_326_, v_a_298_);
v___y_308_ = v___x_327_;
goto v___jp_307_;
}
case 2:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_e_296_);
lean_dec(v_offset_297_);
v___x_328_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4);
v___x_329_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_328_, v_a_298_);
v___y_308_ = v___x_329_;
goto v___jp_307_;
}
case 3:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v_e_296_);
lean_dec(v_offset_297_);
v___x_330_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5);
v___x_331_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_330_, v_a_298_);
v___y_308_ = v___x_331_;
goto v___jp_307_;
}
case 4:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec_ref(v_e_296_);
lean_dec(v_offset_297_);
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6);
v___x_333_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_332_, v_a_298_);
v___y_308_ = v___x_333_;
goto v___jp_307_;
}
case 5:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = l_Lean_Expr_getAppNumArgs(v_e_296_);
v___x_335_ = lean_mk_empty_array_with_capacity(v___x_334_);
lean_dec(v___x_334_);
v___x_336_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_293_, v_stop_294_, v_args_295_, v_offset_297_, v_e_296_, v___x_335_, v_a_298_);
v___y_308_ = v___x_336_;
goto v___jp_307_;
}
case 6:
{
lean_object* v_binderName_337_; lean_object* v_binderType_338_; lean_object* v_body_339_; uint8_t v_binderInfo_340_; lean_object* v___x_341_; lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_fst_347_; lean_object* v_snd_348_; uint8_t v___y_350_; size_t v___x_354_; size_t v___x_355_; uint8_t v___x_356_; 
v_binderName_337_ = lean_ctor_get(v_e_296_, 0);
v_binderType_338_ = lean_ctor_get(v_e_296_, 1);
v_body_339_ = lean_ctor_get(v_e_296_, 2);
v_binderInfo_340_ = lean_ctor_get_uint8(v_e_296_, sizeof(void*)*3 + 8);
lean_inc(v_offset_297_);
lean_inc_ref(v_binderType_338_);
v___x_341_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_binderType_338_, v_offset_297_, v_a_298_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_fst_342_);
v_snd_343_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_snd_343_);
lean_dec_ref(v___x_341_);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v_offset_297_, v___x_344_);
lean_dec(v_offset_297_);
lean_inc_ref(v_body_339_);
v___x_346_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_body_339_, v___x_345_, v_snd_343_);
v_fst_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_fst_347_);
v_snd_348_ = lean_ctor_get(v___x_346_, 1);
lean_inc(v_snd_348_);
lean_dec_ref(v___x_346_);
v___x_354_ = lean_ptr_addr(v_binderType_338_);
v___x_355_ = lean_ptr_addr(v_fst_342_);
v___x_356_ = lean_usize_dec_eq(v___x_354_, v___x_355_);
if (v___x_356_ == 0)
{
v___y_350_ = v___x_356_;
goto v___jp_349_;
}
else
{
size_t v___x_357_; size_t v___x_358_; uint8_t v___x_359_; 
v___x_357_ = lean_ptr_addr(v_body_339_);
v___x_358_ = lean_ptr_addr(v_fst_347_);
v___x_359_ = lean_usize_dec_eq(v___x_357_, v___x_358_);
v___y_350_ = v___x_359_;
goto v___jp_349_;
}
v___jp_349_:
{
if (v___y_350_ == 0)
{
lean_object* v___x_351_; 
lean_inc(v_binderName_337_);
lean_dec_ref(v_e_296_);
v___x_351_ = l_Lean_Expr_lam___override(v_binderName_337_, v_fst_342_, v_fst_347_, v_binderInfo_340_);
v_fst_303_ = v___x_351_;
v_snd_304_ = v_snd_348_;
goto v___jp_302_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_340_, v_binderInfo_340_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_inc(v_binderName_337_);
lean_dec_ref(v_e_296_);
v___x_353_ = l_Lean_Expr_lam___override(v_binderName_337_, v_fst_342_, v_fst_347_, v_binderInfo_340_);
v_fst_303_ = v___x_353_;
v_snd_304_ = v_snd_348_;
goto v___jp_302_;
}
else
{
lean_dec(v_fst_347_);
lean_dec(v_fst_342_);
v_fst_303_ = v_e_296_;
v_snd_304_ = v_snd_348_;
goto v___jp_302_;
}
}
}
}
case 7:
{
lean_object* v_binderName_360_; lean_object* v_binderType_361_; lean_object* v_body_362_; uint8_t v_binderInfo_363_; lean_object* v___x_364_; lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_fst_370_; lean_object* v_snd_371_; uint8_t v___y_373_; size_t v___x_377_; size_t v___x_378_; uint8_t v___x_379_; 
v_binderName_360_ = lean_ctor_get(v_e_296_, 0);
v_binderType_361_ = lean_ctor_get(v_e_296_, 1);
v_body_362_ = lean_ctor_get(v_e_296_, 2);
v_binderInfo_363_ = lean_ctor_get_uint8(v_e_296_, sizeof(void*)*3 + 8);
lean_inc(v_offset_297_);
lean_inc_ref(v_binderType_361_);
v___x_364_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_binderType_361_, v_offset_297_, v_a_298_);
v_fst_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_fst_365_);
v_snd_366_ = lean_ctor_get(v___x_364_, 1);
lean_inc(v_snd_366_);
lean_dec_ref(v___x_364_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v_offset_297_, v___x_367_);
lean_dec(v_offset_297_);
lean_inc_ref(v_body_362_);
v___x_369_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_body_362_, v___x_368_, v_snd_366_);
v_fst_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_fst_370_);
v_snd_371_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_snd_371_);
lean_dec_ref(v___x_369_);
v___x_377_ = lean_ptr_addr(v_binderType_361_);
v___x_378_ = lean_ptr_addr(v_fst_365_);
v___x_379_ = lean_usize_dec_eq(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
v___y_373_ = v___x_379_;
goto v___jp_372_;
}
else
{
size_t v___x_380_; size_t v___x_381_; uint8_t v___x_382_; 
v___x_380_ = lean_ptr_addr(v_body_362_);
v___x_381_ = lean_ptr_addr(v_fst_370_);
v___x_382_ = lean_usize_dec_eq(v___x_380_, v___x_381_);
v___y_373_ = v___x_382_;
goto v___jp_372_;
}
v___jp_372_:
{
if (v___y_373_ == 0)
{
lean_object* v___x_374_; 
lean_inc(v_binderName_360_);
lean_dec_ref(v_e_296_);
v___x_374_ = l_Lean_Expr_forallE___override(v_binderName_360_, v_fst_365_, v_fst_370_, v_binderInfo_363_);
v_fst_303_ = v___x_374_;
v_snd_304_ = v_snd_371_;
goto v___jp_302_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_363_, v_binderInfo_363_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_inc(v_binderName_360_);
lean_dec_ref(v_e_296_);
v___x_376_ = l_Lean_Expr_forallE___override(v_binderName_360_, v_fst_365_, v_fst_370_, v_binderInfo_363_);
v_fst_303_ = v___x_376_;
v_snd_304_ = v_snd_371_;
goto v___jp_302_;
}
else
{
lean_dec(v_fst_370_);
lean_dec(v_fst_365_);
v_fst_303_ = v_e_296_;
v_snd_304_ = v_snd_371_;
goto v___jp_302_;
}
}
}
}
case 8:
{
lean_object* v_declName_383_; lean_object* v_type_384_; lean_object* v_value_385_; lean_object* v_body_386_; uint8_t v_nondep_387_; lean_object* v___x_388_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; lean_object* v_fst_392_; lean_object* v_snd_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_fst_397_; lean_object* v_snd_398_; uint8_t v___y_400_; size_t v___x_406_; size_t v___x_407_; uint8_t v___x_408_; 
v_declName_383_ = lean_ctor_get(v_e_296_, 0);
v_type_384_ = lean_ctor_get(v_e_296_, 1);
v_value_385_ = lean_ctor_get(v_e_296_, 2);
v_body_386_ = lean_ctor_get(v_e_296_, 3);
v_nondep_387_ = lean_ctor_get_uint8(v_e_296_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_297_, 2);
lean_inc_ref(v_type_384_);
v___x_388_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_type_384_, v_offset_297_, v_a_298_);
v_fst_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v___x_388_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v___x_388_);
lean_inc_ref(v_value_385_);
v___x_391_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_value_385_, v_offset_297_, v_snd_390_);
v_fst_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_fst_392_);
v_snd_393_ = lean_ctor_get(v___x_391_, 1);
lean_inc(v_snd_393_);
lean_dec_ref(v___x_391_);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_offset_297_, v___x_394_);
lean_dec(v_offset_297_);
lean_inc_ref(v_body_386_);
v___x_396_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_body_386_, v___x_395_, v_snd_393_);
v_fst_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_fst_397_);
v_snd_398_ = lean_ctor_get(v___x_396_, 1);
lean_inc(v_snd_398_);
lean_dec_ref(v___x_396_);
v___x_406_ = lean_ptr_addr(v_type_384_);
v___x_407_ = lean_ptr_addr(v_fst_389_);
v___x_408_ = lean_usize_dec_eq(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
v___y_400_ = v___x_408_;
goto v___jp_399_;
}
else
{
size_t v___x_409_; size_t v___x_410_; uint8_t v___x_411_; 
v___x_409_ = lean_ptr_addr(v_value_385_);
v___x_410_ = lean_ptr_addr(v_fst_392_);
v___x_411_ = lean_usize_dec_eq(v___x_409_, v___x_410_);
v___y_400_ = v___x_411_;
goto v___jp_399_;
}
v___jp_399_:
{
if (v___y_400_ == 0)
{
lean_object* v___x_401_; 
lean_inc(v_declName_383_);
lean_dec_ref(v_e_296_);
v___x_401_ = l_Lean_Expr_letE___override(v_declName_383_, v_fst_389_, v_fst_392_, v_fst_397_, v_nondep_387_);
v_fst_303_ = v___x_401_;
v_snd_304_ = v_snd_398_;
goto v___jp_302_;
}
else
{
size_t v___x_402_; size_t v___x_403_; uint8_t v___x_404_; 
v___x_402_ = lean_ptr_addr(v_body_386_);
v___x_403_ = lean_ptr_addr(v_fst_397_);
v___x_404_ = lean_usize_dec_eq(v___x_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_inc(v_declName_383_);
lean_dec_ref(v_e_296_);
v___x_405_ = l_Lean_Expr_letE___override(v_declName_383_, v_fst_389_, v_fst_392_, v_fst_397_, v_nondep_387_);
v_fst_303_ = v___x_405_;
v_snd_304_ = v_snd_398_;
goto v___jp_302_;
}
else
{
lean_dec(v_fst_397_);
lean_dec(v_fst_392_);
lean_dec(v_fst_389_);
v_fst_303_ = v_e_296_;
v_snd_304_ = v_snd_398_;
goto v___jp_302_;
}
}
}
}
case 9:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec_ref(v_e_296_);
lean_dec(v_offset_297_);
v___x_412_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_413_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_412_, v_a_298_);
v___y_308_ = v___x_413_;
goto v___jp_307_;
}
case 10:
{
lean_object* v_data_414_; lean_object* v_expr_415_; lean_object* v___x_416_; lean_object* v_fst_417_; lean_object* v_snd_418_; size_t v___x_419_; size_t v___x_420_; uint8_t v___x_421_; 
v_data_414_ = lean_ctor_get(v_e_296_, 0);
v_expr_415_ = lean_ctor_get(v_e_296_, 1);
lean_inc_ref(v_expr_415_);
v___x_416_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_expr_415_, v_offset_297_, v_a_298_);
v_fst_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_fst_417_);
v_snd_418_ = lean_ctor_get(v___x_416_, 1);
lean_inc(v_snd_418_);
lean_dec_ref(v___x_416_);
v___x_419_ = lean_ptr_addr(v_expr_415_);
v___x_420_ = lean_ptr_addr(v_fst_417_);
v___x_421_ = lean_usize_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_inc(v_data_414_);
lean_dec_ref(v_e_296_);
v___x_422_ = l_Lean_Expr_mdata___override(v_data_414_, v_fst_417_);
v_fst_303_ = v___x_422_;
v_snd_304_ = v_snd_418_;
goto v___jp_302_;
}
else
{
lean_dec(v_fst_417_);
v_fst_303_ = v_e_296_;
v_snd_304_ = v_snd_418_;
goto v___jp_302_;
}
}
default: 
{
lean_object* v_typeName_423_; lean_object* v_idx_424_; lean_object* v_struct_425_; lean_object* v___x_426_; lean_object* v_fst_427_; lean_object* v_snd_428_; size_t v___x_429_; size_t v___x_430_; uint8_t v___x_431_; 
v_typeName_423_ = lean_ctor_get(v_e_296_, 0);
v_idx_424_ = lean_ctor_get(v_e_296_, 1);
v_struct_425_ = lean_ctor_get(v_e_296_, 2);
lean_inc_ref(v_struct_425_);
v___x_426_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_293_, v_stop_294_, v_args_295_, v_struct_425_, v_offset_297_, v_a_298_);
v_fst_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_fst_427_);
v_snd_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v___x_426_);
v___x_429_ = lean_ptr_addr(v_struct_425_);
v___x_430_ = lean_ptr_addr(v_fst_427_);
v___x_431_ = lean_usize_dec_eq(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_inc(v_idx_424_);
lean_inc(v_typeName_423_);
lean_dec_ref(v_e_296_);
v___x_432_ = l_Lean_Expr_proj___override(v_typeName_423_, v_idx_424_, v_fst_427_);
v_fst_303_ = v___x_432_;
v_snd_304_ = v_snd_428_;
goto v___jp_302_;
}
else
{
lean_dec(v_fst_427_);
v_fst_303_ = v_e_296_;
v_snd_304_ = v_snd_428_;
goto v___jp_302_;
}
}
}
}
else
{
lean_object* v_val_433_; lean_object* v___x_434_; 
lean_dec_ref(v___x_301_);
lean_dec(v_offset_297_);
lean_dec_ref(v_e_296_);
v_val_433_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_433_);
lean_dec_ref(v___x_311_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v_val_433_);
lean_ctor_set(v___x_434_, 1, v_a_298_);
return v___x_434_;
}
v___jp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc_ref(v_fst_303_);
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(v_snd_304_, v___x_301_, v_fst_303_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_fst_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
return v___x_306_;
}
v___jp_307_:
{
lean_object* v_fst_309_; lean_object* v_snd_310_; 
v_fst_309_ = lean_ctor_get(v___y_308_, 0);
lean_inc(v_fst_309_);
v_snd_310_ = lean_ctor_get(v___y_308_, 1);
lean_inc(v_snd_310_);
lean_dec_ref(v___y_308_);
v_fst_303_ = v_fst_309_;
v_snd_304_ = v_snd_310_;
goto v___jp_302_;
}
}
else
{
lean_object* v___x_435_; 
lean_dec(v_offset_297_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v_e_296_);
lean_ctor_set(v___x_435_, 1, v_a_298_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0(lean_object* v_start_436_, lean_object* v_stop_437_, lean_object* v_args_438_, lean_object* v_offset_439_, size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v_offset_439_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_bs_442_);
lean_ctor_set(v___x_445_, 1, v___y_443_);
return v___x_445_;
}
else
{
lean_object* v_v_446_; lean_object* v___x_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_450_; lean_object* v_bs_x27_451_; size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v_v_446_ = lean_array_uget_borrowed(v_bs_442_, v_i_441_);
lean_inc(v_offset_439_);
lean_inc(v_v_446_);
v___x_447_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_436_, v_stop_437_, v_args_438_, v_v_446_, v_offset_439_, v___y_443_);
v_fst_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_fst_448_);
v_snd_449_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_snd_449_);
lean_dec_ref(v___x_447_);
v___x_450_ = lean_unsigned_to_nat(0u);
v_bs_x27_451_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_450_);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_441_, v___x_452_);
v___x_454_ = lean_array_uset(v_bs_x27_451_, v_i_441_, v_fst_448_);
v_i_441_ = v___x_453_;
v_bs_442_ = v___x_454_;
v___y_443_ = v_snd_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0___boxed(lean_object* v_start_456_, lean_object* v_stop_457_, lean_object* v_args_458_, lean_object* v_offset_459_, lean_object* v_sz_460_, lean_object* v_i_461_, lean_object* v_bs_462_, lean_object* v___y_463_){
_start:
{
size_t v_sz_boxed_464_; size_t v_i_boxed_465_; lean_object* v_res_466_; 
v_sz_boxed_464_ = lean_unbox_usize(v_sz_460_);
lean_dec(v_sz_460_);
v_i_boxed_465_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0(v_start_456_, v_stop_457_, v_args_458_, v_offset_459_, v_sz_boxed_464_, v_i_boxed_465_, v_bs_462_, v___y_463_);
lean_dec_ref(v_args_458_);
lean_dec(v_stop_457_);
lean_dec(v_start_456_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object* v_start_467_, lean_object* v_stop_468_, lean_object* v_args_469_, lean_object* v_offset_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_467_, v_stop_468_, v_args_469_, v_offset_470_, v_x_471_, v_x_472_, v___y_473_);
lean_dec_ref(v_args_469_);
lean_dec(v_stop_468_);
lean_dec(v_start_467_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_475_, lean_object* v_stop_476_, lean_object* v_args_477_, lean_object* v_e_478_, lean_object* v_offset_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_475_, v_stop_476_, v_args_477_, v_e_478_, v_offset_479_, v_a_480_);
lean_dec_ref(v_args_477_);
lean_dec(v_stop_476_);
lean_dec(v_start_475_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1(lean_object* v_00_u03b2_482_, lean_object* v_m_483_, lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(v_m_483_, v_a_484_, v_b_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2(lean_object* v_00_u03b2_487_, lean_object* v_m_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(v_m_488_, v_a_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___boxed(lean_object* v_00_u03b2_491_, lean_object* v_m_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2(v_00_u03b2_491_, v_m_492_, v_a_493_);
lean_dec_ref(v_a_493_);
lean_dec_ref(v_m_492_);
return v_res_494_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1(lean_object* v_00_u03b2_495_, lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(v_a_496_, v_x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_499_, lean_object* v_a_500_, lean_object* v_x_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1(v_00_u03b2_499_, v_a_500_, v_x_501_);
lean_dec(v_x_501_);
lean_dec_ref(v_a_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2(lean_object* v_00_u03b2_504_, lean_object* v_data_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2___redArg(v_data_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3(lean_object* v_00_u03b2_507_, lean_object* v_a_508_, lean_object* v_b_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(v_a_508_, v_b_509_, v_x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5(lean_object* v_00_u03b2_512_, lean_object* v_a_513_, lean_object* v_x_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(v_a_513_, v_x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_516_, lean_object* v_a_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5(v_00_u03b2_516_, v_a_517_, v_x_518_);
lean_dec(v_x_518_);
lean_dec_ref(v_a_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_520_, lean_object* v_i_521_, lean_object* v_source_522_, lean_object* v_target_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4___redArg(v_i_521_, v_source_522_, v_target_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7___redArg(v_x_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_msg_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = l_Lean_instInhabitedExpr;
v___x_531_ = lean_panic_fn_borrowed(v___x_530_, v_msg_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__2(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_534_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__1));
v___x_535_ = lean_unsigned_to_nat(4u);
v___x_536_ = lean_unsigned_to_nat(34u);
v___x_537_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__0));
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_539_ = l_mkPanicMessageWithDecl(v___x_538_, v___x_537_, v___x_536_, v___x_535_, v___x_534_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__3(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_box(0);
v___x_541_ = lean_unsigned_to_nat(16u);
v___x_542_ = lean_mk_array(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__3, &l_Lean_Expr_instantiateBetaRevRange___closed__3_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__3);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_546_, lean_object* v_start_547_, lean_object* v_stop_548_, lean_object* v_args_549_){
_start:
{
uint8_t v___y_551_; uint8_t v___x_560_; 
v___x_560_ = l_Lean_Expr_hasLooseBVars(v_e_546_);
if (v___x_560_ == 0)
{
v___y_551_ = v___x_560_;
goto v___jp_550_;
}
else
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_lt(v_start_547_, v_stop_548_);
v___y_551_ = v___x_561_;
goto v___jp_550_;
}
v___jp_550_:
{
if (v___y_551_ == 0)
{
return v_e_546_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_array_get_size(v_args_549_);
v___x_553_ = lean_nat_dec_le(v_stop_548_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v_e_546_);
v___x_554_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__2, &l_Lean_Expr_instantiateBetaRevRange___closed__2_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__2);
v___x_555_ = l_panic___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v___x_554_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_fst_559_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__4, &l_Lean_Expr_instantiateBetaRevRange___closed__4_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__4);
v___x_558_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_547_, v_stop_548_, v_args_549_, v_e_546_, v___x_556_, v___x_557_);
v_fst_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_fst_559_);
lean_dec_ref(v___x_558_);
return v_fst_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_562_, lean_object* v_start_563_, lean_object* v_stop_564_, lean_object* v_args_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Expr_instantiateBetaRevRange(v_e_562_, v_start_563_, v_stop_564_, v_args_565_);
lean_dec_ref(v_args_565_);
lean_dec(v_stop_564_);
lean_dec(v_start_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v_env_574_; lean_object* v___x_575_; lean_object* v_mctx_576_; lean_object* v_lctx_577_; lean_object* v_options_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_env_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_env_574_);
lean_dec(v___x_573_);
v___x_575_ = lean_st_ref_get(v___y_569_);
v_mctx_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_mctx_576_);
lean_dec(v___x_575_);
v_lctx_577_ = lean_ctor_get(v___y_568_, 2);
v_options_578_ = lean_ctor_get(v___y_570_, 2);
lean_inc_ref(v_options_578_);
lean_inc_ref(v_lctx_577_);
v___x_579_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_579_, 0, v_env_574_);
lean_ctor_set(v___x_579_, 1, v_mctx_576_);
lean_ctor_set(v___x_579_, 2, v_lctx_577_);
lean_ctor_set(v___x_579_, 3, v_options_578_);
v___x_580_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_msgData_567_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_ref_595_; lean_object* v___x_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_ref_595_ = lean_ctor_get(v___y_592_, 5);
v___x_596_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_605_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_inc(v_ref_595_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v_ref_595_);
lean_ctor_set(v___x_601_, 1, v_a_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 1);
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_612_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_615_ = l_Lean_stringToMessageData(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_623_ = l_Lean_indentExpr(v_f_616_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_624_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_633_, lean_object* v_f_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_641_, lean_object* v_f_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_641_, v_f_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_665_, lean_object* v_args_666_, lean_object* v_f_667_, lean_object* v_a_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_a_676_; uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_lt(v_a_668_, v_upperBound_665_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_dec(v_a_668_);
lean_dec_ref(v_f_667_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v_b_669_);
return v___x_681_;
}
else
{
lean_object* v_fst_682_; 
v_fst_682_ = lean_ctor_get(v_b_669_, 0);
lean_inc(v_fst_682_);
if (lean_obj_tag(v_fst_682_) == 7)
{
lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_691_; 
v_snd_683_ = lean_ctor_get(v_b_669_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_b_669_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v_b_669_, 0);
lean_dec(v_unused_692_);
v___x_685_ = v_b_669_;
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_dec(v_b_669_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_body_687_; lean_object* v___x_689_; 
v_body_687_ = lean_ctor_get(v_fst_682_, 2);
lean_inc_ref(v_body_687_);
lean_dec_ref(v_fst_682_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v_body_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_body_687_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_snd_683_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_a_676_ = v___x_689_;
goto v___jp_675_;
}
}
}
else
{
lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_728_; 
v_snd_693_ = lean_ctor_get(v_b_669_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_b_669_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v_b_669_, 0);
lean_dec(v_unused_729_);
v___x_695_ = v_b_669_;
v_isShared_696_ = v_isSharedCheck_728_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_dec(v_b_669_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_728_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_inc(v_fst_682_);
v___x_697_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_682_, v_snd_693_, v_a_668_, v_args_666_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
v___x_698_ = lean_whnf(v___x_697_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
if (lean_obj_tag(v_a_699_) == 7)
{
lean_object* v_body_700_; lean_object* v___x_702_; 
lean_dec(v_snd_693_);
lean_dec(v_fst_682_);
v_body_700_ = lean_ctor_get(v_a_699_, 2);
lean_inc_ref(v_body_700_);
lean_dec_ref(v_a_699_);
lean_inc(v_a_668_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_a_668_);
lean_ctor_set(v___x_695_, 0, v_body_700_);
v___x_702_ = v___x_695_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_body_700_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_a_668_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
v_a_676_ = v___x_702_;
goto v___jp_675_;
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_a_699_);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_add(v_a_668_, v___x_705_);
lean_inc_ref(v_f_667_);
v___x_707_ = l_Lean_mkAppRange(v_f_667_, v___x_704_, v___x_706_, v_args_666_);
lean_dec(v___x_706_);
v___x_708_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_707_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v___x_708_);
if (v_isShared_696_ == 0)
{
v___x_710_ = v___x_695_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_682_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_snd_693_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v_a_676_ = v___x_710_;
goto v___jp_675_;
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_del_object(v___x_695_);
lean_dec(v_snd_693_);
lean_dec(v_fst_682_);
lean_dec(v_a_668_);
lean_dec_ref(v_f_667_);
v_a_712_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_708_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
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
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_del_object(v___x_695_);
lean_dec(v_snd_693_);
lean_dec(v_fst_682_);
lean_dec(v_a_668_);
lean_dec_ref(v_f_667_);
v_a_720_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_698_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_698_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_add(v_a_668_, v___x_677_);
lean_dec(v_a_668_);
v_a_668_ = v___x_678_;
v_b_669_ = v_a_676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_730_, lean_object* v_args_731_, lean_object* v_f_732_, lean_object* v_a_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_730_, v_args_731_, v_f_732_, v_a_733_, v_b_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec_ref(v_args_731_);
lean_dec(v_upperBound_730_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_741_, lean_object* v_args_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v___x_748_; 
lean_inc(v_a_746_);
lean_inc_ref(v_a_745_);
lean_inc(v_a_744_);
lean_inc_ref(v_a_743_);
lean_inc_ref(v_f_741_);
v___x_748_ = lean_infer_type(v_f_741_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_array_get_size(v_args_742_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_a_749_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_750_, v_args_742_, v_f_741_, v___x_751_, v___x_752_, v_a_743_, v_a_744_, v_a_745_, v_a_746_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_764_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_764_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_fst_758_; lean_object* v_snd_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v_fst_758_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_fst_758_);
v_snd_759_ = lean_ctor_get(v_a_754_, 1);
lean_inc(v_snd_759_);
lean_dec(v_a_754_);
v___x_760_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_758_, v_snd_759_, v___x_750_, v_args_742_);
lean_dec(v_snd_759_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_760_);
v___x_762_ = v___x_756_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_765_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_753_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_753_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_dec_ref(v_f_741_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_773_, lean_object* v_args_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_773_, v_args_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec_ref(v_args_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_781_, lean_object* v_args_782_, lean_object* v_f_783_, lean_object* v_inst_784_, lean_object* v_R_785_, lean_object* v_a_786_, lean_object* v_b_787_, lean_object* v_c_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_781_, v_args_782_, v_f_783_, v_a_786_, v_b_787_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_795_, lean_object* v_args_796_, lean_object* v_f_797_, lean_object* v_inst_798_, lean_object* v_R_799_, lean_object* v_a_800_, lean_object* v_b_801_, lean_object* v_c_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_795_, v_args_796_, v_f_797_, v_inst_798_, v_R_799_, v_a_800_, v_b_801_, v_c_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_args_796_);
lean_dec(v_upperBound_795_);
return v_res_808_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_812_, lean_object* v_us_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_819_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_820_ = l_Lean_mkConst(v_constName_812_, v_us_813_);
v___x_821_ = l_Lean_MessageData_ofExpr(v___x_820_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_819_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_822_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_824_, lean_object* v_us_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_824_, v_us_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_832_, lean_object* v_constName_833_, lean_object* v_us_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_833_, v_us_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_841_, lean_object* v_constName_842_, lean_object* v_us_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_841_, v_constName_842_, v_us_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_850_, lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_fileName_857_; lean_object* v_fileMap_858_; lean_object* v_options_859_; lean_object* v_currRecDepth_860_; lean_object* v_maxRecDepth_861_; lean_object* v_ref_862_; lean_object* v_currNamespace_863_; lean_object* v_openDecls_864_; lean_object* v_initHeartbeats_865_; lean_object* v_maxHeartbeats_866_; lean_object* v_quotContext_867_; lean_object* v_currMacroScope_868_; uint8_t v_diag_869_; lean_object* v_cancelTk_x3f_870_; uint8_t v_suppressElabErrors_871_; lean_object* v_inheritedTraceOptions_872_; lean_object* v_ref_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_fileName_857_ = lean_ctor_get(v___y_854_, 0);
v_fileMap_858_ = lean_ctor_get(v___y_854_, 1);
v_options_859_ = lean_ctor_get(v___y_854_, 2);
v_currRecDepth_860_ = lean_ctor_get(v___y_854_, 3);
v_maxRecDepth_861_ = lean_ctor_get(v___y_854_, 4);
v_ref_862_ = lean_ctor_get(v___y_854_, 5);
v_currNamespace_863_ = lean_ctor_get(v___y_854_, 6);
v_openDecls_864_ = lean_ctor_get(v___y_854_, 7);
v_initHeartbeats_865_ = lean_ctor_get(v___y_854_, 8);
v_maxHeartbeats_866_ = lean_ctor_get(v___y_854_, 9);
v_quotContext_867_ = lean_ctor_get(v___y_854_, 10);
v_currMacroScope_868_ = lean_ctor_get(v___y_854_, 11);
v_diag_869_ = lean_ctor_get_uint8(v___y_854_, sizeof(void*)*14);
v_cancelTk_x3f_870_ = lean_ctor_get(v___y_854_, 12);
v_suppressElabErrors_871_ = lean_ctor_get_uint8(v___y_854_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_872_ = lean_ctor_get(v___y_854_, 13);
v_ref_873_ = l_Lean_replaceRef(v_ref_850_, v_ref_862_);
lean_inc_ref(v_inheritedTraceOptions_872_);
lean_inc(v_cancelTk_x3f_870_);
lean_inc(v_currMacroScope_868_);
lean_inc(v_quotContext_867_);
lean_inc(v_maxHeartbeats_866_);
lean_inc(v_initHeartbeats_865_);
lean_inc(v_openDecls_864_);
lean_inc(v_currNamespace_863_);
lean_inc(v_maxRecDepth_861_);
lean_inc(v_currRecDepth_860_);
lean_inc_ref(v_options_859_);
lean_inc_ref(v_fileMap_858_);
lean_inc_ref(v_fileName_857_);
v___x_874_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_874_, 0, v_fileName_857_);
lean_ctor_set(v___x_874_, 1, v_fileMap_858_);
lean_ctor_set(v___x_874_, 2, v_options_859_);
lean_ctor_set(v___x_874_, 3, v_currRecDepth_860_);
lean_ctor_set(v___x_874_, 4, v_maxRecDepth_861_);
lean_ctor_set(v___x_874_, 5, v_ref_873_);
lean_ctor_set(v___x_874_, 6, v_currNamespace_863_);
lean_ctor_set(v___x_874_, 7, v_openDecls_864_);
lean_ctor_set(v___x_874_, 8, v_initHeartbeats_865_);
lean_ctor_set(v___x_874_, 9, v_maxHeartbeats_866_);
lean_ctor_set(v___x_874_, 10, v_quotContext_867_);
lean_ctor_set(v___x_874_, 11, v_currMacroScope_868_);
lean_ctor_set(v___x_874_, 12, v_cancelTk_x3f_870_);
lean_ctor_set(v___x_874_, 13, v_inheritedTraceOptions_872_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*14, v_diag_869_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*14 + 1, v_suppressElabErrors_871_);
v___x_875_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_851_, v___y_852_, v___y_853_, v___x_874_, v___y_855_);
lean_dec_ref(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_876_, lean_object* v_msg_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_876_, v_msg_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v_ref_876_);
return v_res_883_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_884_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
lean_ctor_set(v___x_889_, 3, v___x_888_);
lean_ctor_set(v___x_889_, 4, v___x_887_);
lean_ctor_set(v___x_889_, 5, v___x_887_);
lean_ctor_set(v___x_889_, 6, v___x_887_);
lean_ctor_set(v___x_889_, 7, v___x_887_);
lean_ctor_set(v___x_889_, 8, v___x_887_);
lean_ctor_set(v___x_889_, 9, v___x_887_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_unsigned_to_nat(32u);
v___x_891_ = lean_mk_empty_array_with_capacity(v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_893_ = ((size_t)5ULL);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_unsigned_to_nat(32u);
v___x_896_ = lean_mk_empty_array_with_capacity(v___x_895_);
v___x_897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_898_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_896_);
lean_ctor_set(v___x_898_, 2, v___x_894_);
lean_ctor_set(v___x_898_, 3, v___x_894_);
lean_ctor_set_usize(v___x_898_, 4, v___x_893_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_899_ = lean_box(1);
v___x_900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_900_);
lean_ctor_set(v___x_902_, 2, v___x_899_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_920_ = l_Lean_stringToMessageData(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_924_, lean_object* v_declHint_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_env_929_; uint8_t v___x_930_; 
v___x_928_ = lean_st_ref_get(v___y_926_);
v_env_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_ref(v_env_929_);
lean_dec(v___x_928_);
v___x_930_ = l_Lean_Name_isAnonymous(v_declHint_925_);
if (v___x_930_ == 0)
{
uint8_t v_isExporting_931_; 
v_isExporting_931_ = lean_ctor_get_uint8(v_env_929_, sizeof(void*)*8);
if (v_isExporting_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v_env_929_);
lean_dec(v_declHint_925_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_msg_924_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; uint8_t v___x_934_; 
lean_inc_ref(v_env_929_);
v___x_933_ = l_Lean_Environment_setExporting(v_env_929_, v___x_930_);
lean_inc(v_declHint_925_);
lean_inc_ref(v___x_933_);
v___x_934_ = l_Lean_Environment_contains(v___x_933_, v_declHint_925_, v_isExporting_931_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec_ref(v___x_933_);
lean_dec_ref(v_env_929_);
lean_dec(v_declHint_925_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_msg_924_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_c_941_; lean_object* v___x_942_; 
v___x_936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_938_ = l_Lean_Options_empty;
v___x_939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_939_, 0, v___x_933_);
lean_ctor_set(v___x_939_, 1, v___x_936_);
lean_ctor_set(v___x_939_, 2, v___x_937_);
lean_ctor_set(v___x_939_, 3, v___x_938_);
lean_inc(v_declHint_925_);
v___x_940_ = l_Lean_MessageData_ofConstName(v_declHint_925_, v___x_930_);
v_c_941_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_941_, 0, v___x_939_);
lean_ctor_set(v_c_941_, 1, v___x_940_);
v___x_942_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_929_, v_declHint_925_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec_ref(v_env_929_);
lean_dec(v_declHint_925_);
v___x_943_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_c_941_);
v___x_945_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_MessageData_note(v___x_946_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v_msg_924_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
else
{
lean_object* v_val_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_985_; 
v_val_950_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_985_ == 0)
{
v___x_952_ = v___x_942_;
v_isShared_953_ = v_isSharedCheck_985_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_val_950_);
lean_dec(v___x_942_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_985_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_mod_957_; uint8_t v___x_958_; 
v___x_954_ = lean_box(0);
v___x_955_ = l_Lean_Environment_header(v_env_929_);
lean_dec_ref(v_env_929_);
v___x_956_ = l_Lean_EnvironmentHeader_moduleNames(v___x_955_);
v_mod_957_ = lean_array_get(v___x_954_, v___x_956_, v_val_950_);
lean_dec(v_val_950_);
lean_dec_ref(v___x_956_);
v___x_958_ = l_Lean_isPrivateName(v_declHint_925_);
lean_dec(v_declHint_925_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_959_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v_c_941_);
v___x_961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_MessageData_ofName(v_mod_957_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_MessageData_note(v___x_966_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v_msg_924_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 0);
lean_ctor_set(v___x_952_, 0, v___x_968_);
v___x_970_ = v___x_952_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v_c_941_);
v___x_974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_Lean_MessageData_ofName(v_mod_957_);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = l_Lean_MessageData_note(v___x_979_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v_msg_924_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
if (v_isShared_953_ == 0)
{
lean_ctor_set_tag(v___x_952_, 0);
lean_ctor_set(v___x_952_, 0, v___x_981_);
v___x_983_ = v___x_952_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_986_; 
lean_dec_ref(v_env_929_);
lean_dec(v_declHint_925_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_msg_924_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_987_, lean_object* v_declHint_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_987_, v_declHint_988_, v___y_989_);
lean_dec(v___y_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_992_, lean_object* v_declHint_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1009_; 
v___x_999_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_992_, v_declHint_993_, v___y_997_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1004_ = l_Lean_unknownIdentifierMessageTag;
v___x_1005_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_1000_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1005_);
v___x_1007_ = v___x_1002_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1010_, lean_object* v_declHint_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1010_, v_declHint_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1018_, lean_object* v_msg_1019_, lean_object* v_declHint_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1019_, v_declHint_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1018_, v_a_1027_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1029_, lean_object* v_msg_1030_, lean_object* v_declHint_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1029_, v_msg_1030_, v_declHint_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v_ref_1029_);
return v_res_1037_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1044_, lean_object* v_constName_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1051_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1052_ = 0;
lean_inc(v_constName_1045_);
v___x_1053_ = l_Lean_MessageData_ofConstName(v_constName_1045_, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1051_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1044_, v___x_1056_, v_constName_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1058_, lean_object* v_constName_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1058_, v_constName_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v_ref_1058_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_ref_1072_; lean_object* v___x_1073_; 
v_ref_1072_ = lean_ctor_get(v___y_1069_, 5);
v___x_1073_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1072_, v_constName_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v_env_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1087_ = lean_st_ref_get(v___y_1085_);
v_env_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_env_1088_);
lean_dec(v___x_1087_);
v___x_1089_ = 0;
lean_inc(v_constName_1081_);
v___x_1090_ = l_Lean_Environment_findConstVal_x3f(v_env_1088_, v_constName_1081_, v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
return v___x_1091_;
}
else
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_constName_1081_);
v_val_1092_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1090_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v___x_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 0);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_val_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1107_, lean_object* v_us_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; 
lean_inc(v_c_1107_);
v___x_1114_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1107_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v_levelParams_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v___x_1114_);
v_levelParams_1116_ = lean_ctor_get(v_a_1115_, 1);
v___x_1117_ = l_List_lengthTR___redArg(v_levelParams_1116_);
v___x_1118_ = l_List_lengthTR___redArg(v_us_1108_);
v___x_1119_ = lean_nat_dec_eq(v___x_1117_, v___x_1118_);
lean_dec(v___x_1118_);
lean_dec(v___x_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec(v_a_1115_);
v___x_1120_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1107_, v_us_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; 
lean_dec(v_c_1107_);
v___x_1121_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1115_, v_us_1108_, v_a_1112_);
return v___x_1121_;
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v_us_1108_);
lean_dec(v_c_1107_);
v_a_1122_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1114_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1114_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1130_, lean_object* v_us_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1130_, v_us_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1138_, lean_object* v_constName_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_constName_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1146_, v_constName_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1154_, lean_object* v_ref_1155_, lean_object* v_constName_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1155_, v_constName_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1163_, lean_object* v_ref_1164_, lean_object* v_constName_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1163_, v_ref_1164_, v_constName_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v_ref_1164_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1172_, lean_object* v_ref_1173_, lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1173_, v_msg_1174_, v_declHint_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_ref_1183_, lean_object* v_msg_1184_, lean_object* v_declHint_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1182_, v_ref_1183_, v_msg_1184_, v_declHint_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v_ref_1183_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1192_, lean_object* v_declHint_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1192_, v_declHint_1193_, v___y_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1200_, lean_object* v_declHint_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1200_, v_declHint_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1208_, lean_object* v_ref_1209_, lean_object* v_msg_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1209_, v_msg_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_ref_1218_, lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1217_, v_ref_1218_, v_msg_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v_ref_1218_);
return v_res_1225_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1232_, lean_object* v_idx_1233_, lean_object* v_e_1234_, lean_object* v_a_1235_, lean_object* v_00_u03b1_1236_, lean_object* v_x_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1243_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1244_ = l_Lean_mkProj(v_structName_1232_, v_idx_1233_, v_e_1234_);
v___x_1245_ = l_Lean_indentExpr(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1243_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = l_Lean_indentExpr(v_a_1235_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1250_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1252_, lean_object* v_idx_1253_, lean_object* v_e_1254_, lean_object* v_a_1255_, lean_object* v_00_u03b1_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1252_, v_idx_1253_, v_e_1254_, v_a_1255_, v_00_u03b1_1256_, v_x_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v_env_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1270_ = lean_st_ref_get(v___y_1268_);
v_env_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc_ref(v_env_1271_);
lean_dec(v___x_1270_);
v___x_1272_ = 0;
lean_inc(v_constName_1264_);
v___x_1273_ = l_Lean_Environment_find_x3f(v_env_1271_, v_constName_1264_, v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1274_;
}
else
{
lean_object* v_val_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_constName_1264_);
v_val_1275_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1273_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_val_1275_);
lean_dec(v___x_1273_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 0);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_val_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1290_, lean_object* v_structName_1291_, lean_object* v_e_1292_, lean_object* v_idx_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_a_1303_; uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_lt(v_a_1295_, v_upperBound_1290_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_idx_1293_);
lean_dec_ref(v_e_1292_);
lean_dec(v_structName_1291_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_b_1296_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; 
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
v___x_1309_ = lean_whnf(v_b_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1309_);
if (lean_obj_tag(v_a_1310_) == 7)
{
lean_object* v_body_1311_; uint8_t v___x_1312_; 
v_body_1311_ = lean_ctor_get(v_a_1310_, 2);
lean_inc_ref(v_body_1311_);
lean_dec_ref(v_a_1310_);
v___x_1312_ = l_Lean_Expr_hasLooseBVars(v_body_1311_);
if (v___x_1312_ == 0)
{
v_a_1303_ = v_body_1311_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_inc_ref(v_e_1292_);
lean_inc(v_a_1295_);
lean_inc(v_structName_1291_);
v___x_1313_ = l_Lean_mkProj(v_structName_1291_, v_a_1295_, v_e_1292_);
v___x_1314_ = lean_expr_instantiate1(v_body_1311_, v___x_1313_);
lean_dec_ref(v___x_1313_);
lean_dec_ref(v_body_1311_);
v_a_1303_ = v___x_1314_;
goto v___jp_1302_;
}
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1315_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1292_);
lean_inc(v_idx_1293_);
lean_inc(v_structName_1291_);
v___x_1316_ = l_Lean_mkProj(v_structName_1291_, v_idx_1293_, v_e_1292_);
v___x_1317_ = l_Lean_indentExpr(v___x_1316_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1315_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
lean_inc_ref(v_a_1294_);
v___x_1321_ = l_Lean_indentExpr(v_a_1294_);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1322_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_dec_ref(v___x_1323_);
v_a_1303_ = v_a_1310_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_a_1310_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_idx_1293_);
lean_dec_ref(v_e_1292_);
lean_dec(v_structName_1291_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_idx_1293_);
lean_dec_ref(v_e_1292_);
lean_dec(v_structName_1291_);
return v___x_1309_;
}
}
v___jp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_add(v_a_1295_, v___x_1304_);
lean_dec(v_a_1295_);
v_a_1295_ = v___x_1305_;
v_b_1296_ = v_a_1303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1332_, lean_object* v_structName_1333_, lean_object* v_e_1334_, lean_object* v_idx_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1332_, v_structName_1333_, v_e_1334_, v_idx_1335_, v_a_1336_, v_a_1337_, v_b_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v_upperBound_1332_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1345_, lean_object* v_structName_1346_, lean_object* v_e_1347_, lean_object* v_idx_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_a_1358_; uint8_t v___x_1362_; 
v___x_1362_ = lean_nat_dec_lt(v_a_1350_, v_upperBound_1345_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; 
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_idx_1348_);
lean_dec_ref(v_e_1347_);
lean_dec(v_structName_1346_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_b_1351_);
return v___x_1363_;
}
else
{
lean_object* v___x_1364_; 
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
v___x_1364_ = lean_whnf(v_b_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
if (lean_obj_tag(v_a_1365_) == 7)
{
lean_object* v_body_1366_; uint8_t v___x_1367_; 
v_body_1366_ = lean_ctor_get(v_a_1365_, 2);
lean_inc_ref(v_body_1366_);
lean_dec_ref(v_a_1365_);
v___x_1367_ = l_Lean_Expr_hasLooseBVars(v_body_1366_);
if (v___x_1367_ == 0)
{
v_a_1358_ = v_body_1366_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_inc_ref(v_e_1347_);
lean_inc(v_a_1350_);
lean_inc(v_structName_1346_);
v___x_1368_ = l_Lean_mkProj(v_structName_1346_, v_a_1350_, v_e_1347_);
v___x_1369_ = lean_expr_instantiate1(v_body_1366_, v___x_1368_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v_body_1366_);
v_a_1358_ = v___x_1369_;
goto v___jp_1357_;
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1370_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1347_);
lean_inc(v_idx_1348_);
lean_inc(v_structName_1346_);
v___x_1371_ = l_Lean_mkProj(v_structName_1346_, v_idx_1348_, v_e_1347_);
v___x_1372_ = l_Lean_indentExpr(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1370_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
lean_inc_ref(v_a_1349_);
v___x_1376_ = l_Lean_indentExpr(v_a_1349_);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1377_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_dec_ref(v___x_1378_);
v_a_1358_ = v_a_1365_;
goto v___jp_1357_;
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1365_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_idx_1348_);
lean_dec_ref(v_e_1347_);
lean_dec(v_structName_1346_);
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
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
else
{
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_idx_1348_);
lean_dec_ref(v_e_1347_);
lean_dec(v_structName_1346_);
return v___x_1364_;
}
}
v___jp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_nat_add(v_a_1350_, v___x_1359_);
lean_dec(v_a_1350_);
v___x_1361_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1345_, v_structName_1346_, v_e_1347_, v_idx_1348_, v_a_1349_, v___x_1360_, v_a_1358_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1387_, lean_object* v_structName_1388_, lean_object* v_e_1389_, lean_object* v_idx_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_b_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1387_, v_structName_1388_, v_e_1389_, v_idx_1390_, v_a_1391_, v_a_1392_, v_b_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v_upperBound_1387_);
return v_res_1399_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1400_; lean_object* v_dummy_1401_; 
v___x_1400_ = lean_box(0);
v_dummy_1401_ = l_Lean_Expr_sort___override(v___x_1400_);
return v_dummy_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1402_, lean_object* v_idx_1403_, lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v___x_1410_; 
lean_inc(v_a_1408_);
lean_inc_ref(v_a_1407_);
lean_inc(v_a_1406_);
lean_inc_ref(v_a_1405_);
lean_inc_ref(v_e_1404_);
v___x_1410_ = lean_infer_type(v_e_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref(v___x_1410_);
lean_inc(v_a_1408_);
lean_inc_ref(v_a_1407_);
lean_inc(v_a_1406_);
lean_inc_ref(v_a_1405_);
v___x_1412_ = lean_whnf(v_a_1411_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = l_Lean_Expr_getAppFn(v_a_1413_);
if (lean_obj_tag(v___x_1414_) == 4)
{
lean_object* v_declName_1415_; lean_object* v_us_1416_; lean_object* v___x_1417_; lean_object* v_env_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v_declName_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_declName_1415_);
v_us_1416_ = lean_ctor_get(v___x_1414_, 1);
lean_inc(v_us_1416_);
lean_dec_ref(v___x_1414_);
v___x_1417_ = lean_st_ref_get(v_a_1408_);
v_env_1421_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_env_1421_);
lean_dec(v___x_1417_);
v___x_1422_ = 0;
v___x_1423_ = l_Lean_Environment_find_x3f(v_env_1421_, v_declName_1415_, v___x_1422_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_us_1416_);
v___x_1424_ = lean_box(0);
v___x_1425_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1424_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
return v___x_1425_;
}
else
{
lean_object* v_val_1426_; 
v_val_1426_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v___x_1423_);
if (lean_obj_tag(v_val_1426_) == 5)
{
lean_object* v_val_1427_; lean_object* v_ctors_1428_; 
v_val_1427_ = lean_ctor_get(v_val_1426_, 0);
lean_inc_ref(v_val_1427_);
lean_dec_ref(v_val_1426_);
v_ctors_1428_ = lean_ctor_get(v_val_1427_, 4);
lean_inc(v_ctors_1428_);
if (lean_obj_tag(v_ctors_1428_) == 1)
{
lean_object* v_tail_1429_; 
v_tail_1429_ = lean_ctor_get(v_ctors_1428_, 1);
if (lean_obj_tag(v_tail_1429_) == 0)
{
lean_object* v_toConstantVal_1430_; lean_object* v_numParams_1431_; lean_object* v_numIndices_1432_; lean_object* v_head_1433_; lean_object* v___x_1434_; 
v_toConstantVal_1430_ = lean_ctor_get(v_val_1427_, 0);
lean_inc_ref(v_toConstantVal_1430_);
v_numParams_1431_ = lean_ctor_get(v_val_1427_, 1);
lean_inc(v_numParams_1431_);
v_numIndices_1432_ = lean_ctor_get(v_val_1427_, 2);
lean_inc(v_numIndices_1432_);
lean_dec_ref(v_val_1427_);
v_head_1433_ = lean_ctor_get(v_ctors_1428_, 0);
lean_inc(v_head_1433_);
lean_dec_ref(v_ctors_1428_);
v___x_1434_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1433_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
if (lean_obj_tag(v_a_1435_) == 6)
{
lean_object* v_val_1436_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v_name_1476_; uint8_t v___x_1477_; 
v_val_1436_ = lean_ctor_get(v_a_1435_, 0);
lean_inc_ref(v_val_1436_);
lean_dec_ref(v_a_1435_);
v_name_1476_ = lean_ctor_get(v_toConstantVal_1430_, 0);
lean_inc(v_name_1476_);
lean_dec_ref(v_toConstantVal_1430_);
v___x_1477_ = lean_name_eq(v_name_1476_, v_structName_1402_);
lean_dec(v_name_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_val_1436_);
lean_dec(v_numIndices_1432_);
lean_dec(v_numParams_1431_);
lean_dec(v_us_1416_);
v___x_1478_ = lean_box(0);
v___x_1479_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1478_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
v___y_1438_ = v_a_1405_;
v___y_1439_ = v_a_1406_;
v___y_1440_ = v_a_1407_;
v___y_1441_ = v_a_1408_;
goto v___jp_1437_;
}
v___jp_1437_:
{
lean_object* v_dummy_1442_; lean_object* v_nargs_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_dummy_1442_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1443_ = l_Lean_Expr_getAppNumArgs(v_a_1413_);
lean_inc(v_nargs_1443_);
v___x_1444_ = lean_mk_array(v_nargs_1443_, v_dummy_1442_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_sub(v_nargs_1443_, v___x_1445_);
lean_dec(v_nargs_1443_);
lean_inc(v_a_1413_);
v___x_1447_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1413_, v___x_1444_, v___x_1446_);
v___x_1448_ = lean_nat_add(v_numParams_1431_, v_numIndices_1432_);
lean_dec(v_numIndices_1432_);
v___x_1449_ = lean_array_get_size(v___x_1447_);
v___x_1450_ = lean_nat_dec_eq(v___x_1448_, v___x_1449_);
lean_dec(v___x_1448_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v___x_1447_);
lean_dec_ref(v_val_1436_);
lean_dec(v_numParams_1431_);
lean_dec(v_us_1416_);
v___x_1451_ = lean_box(0);
v___x_1452_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1451_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1452_;
}
else
{
lean_object* v_toConstantVal_1453_; lean_object* v_name_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_toConstantVal_1453_ = lean_ctor_get(v_val_1436_, 0);
lean_inc_ref(v_toConstantVal_1453_);
lean_dec_ref(v_val_1436_);
v_name_1454_ = lean_ctor_get(v_toConstantVal_1453_, 0);
lean_inc(v_name_1454_);
lean_dec_ref(v_toConstantVal_1453_);
v___x_1455_ = l_Lean_mkConst(v_name_1454_, v_us_1416_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = l_Array_toSubarray___redArg(v___x_1447_, v___x_1456_, v_numParams_1431_);
v___x_1458_ = l_Subarray_copy___redArg(v___x_1457_);
v___x_1459_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1455_, v___x_1458_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec_ref(v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1461_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
lean_inc(v_a_1413_);
lean_inc_ref(v_e_1404_);
lean_inc(v_structName_1402_);
lean_inc(v_idx_1403_);
v___x_1461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1403_, v_structName_1402_, v_e_1404_, v_idx_1403_, v_a_1413_, v___x_1456_, v_a_1460_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
v___x_1463_ = lean_whnf(v_a_1462_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1475_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1475_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1475_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
if (lean_obj_tag(v_a_1464_) == 7)
{
lean_object* v_binderType_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_dec(v_a_1413_);
lean_dec_ref(v_e_1404_);
lean_dec(v_idx_1403_);
lean_dec(v_structName_1402_);
v_binderType_1468_ = lean_ctor_get(v_a_1464_, 1);
lean_inc_ref(v_binderType_1468_);
lean_dec_ref(v_a_1464_);
v___x_1469_ = lean_expr_consume_type_annotations(v_binderType_1468_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1469_);
v___x_1471_ = v___x_1466_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_del_object(v___x_1466_);
lean_dec(v_a_1464_);
v___x_1473_ = lean_box(0);
v___x_1474_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1473_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1474_;
}
}
}
else
{
lean_dec(v_a_1413_);
lean_dec_ref(v_e_1404_);
lean_dec(v_idx_1403_);
lean_dec(v_structName_1402_);
return v___x_1463_;
}
}
else
{
lean_dec(v_a_1413_);
lean_dec_ref(v_e_1404_);
lean_dec(v_idx_1403_);
lean_dec(v_structName_1402_);
return v___x_1461_;
}
}
else
{
lean_dec(v_a_1413_);
lean_dec_ref(v_e_1404_);
lean_dec(v_idx_1403_);
lean_dec(v_structName_1402_);
return v___x_1459_;
}
}
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec(v_a_1435_);
lean_dec(v_numIndices_1432_);
lean_dec(v_numParams_1431_);
lean_dec_ref(v_toConstantVal_1430_);
lean_dec(v_us_1416_);
v___x_1488_ = lean_box(0);
v___x_1489_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1488_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
return v___x_1489_;
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_numIndices_1432_);
lean_dec(v_numParams_1431_);
lean_dec_ref(v_toConstantVal_1430_);
lean_dec(v_us_1416_);
lean_dec(v_a_1413_);
lean_dec_ref(v_e_1404_);
lean_dec(v_idx_1403_);
lean_dec(v_structName_1402_);
v_a_1490_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1434_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1434_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_dec_ref(v_ctors_1428_);
lean_dec_ref(v_val_1427_);
lean_dec(v_us_1416_);
goto v___jp_1418_;
}
}
else
{
lean_dec(v_ctors_1428_);
lean_dec_ref(v_val_1427_);
lean_dec(v_us_1416_);
goto v___jp_1418_;
}
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec(v_val_1426_);
lean_dec(v_us_1416_);
v___x_1498_ = lean_box(0);
v___x_1499_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1498_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
return v___x_1499_;
}
}
v___jp_1418_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1419_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
return v___x_1420_;
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v___x_1414_);
v___x_1500_ = lean_box(0);
v___x_1501_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1402_, v_idx_1403_, v_e_1404_, v_a_1413_, lean_box(0), v___x_1500_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
return v___x_1501_;
}
}
else
{
lean_dec_ref(v_e_1404_);
lean_dec(v_idx_1403_);
lean_dec(v_structName_1402_);
return v___x_1412_;
}
}
else
{
lean_dec_ref(v_e_1404_);
lean_dec(v_idx_1403_);
lean_dec(v_structName_1402_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1502_, lean_object* v_idx_1503_, lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1502_, v_idx_1503_, v_e_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1511_, lean_object* v_structName_1512_, lean_object* v_e_1513_, lean_object* v_idx_1514_, lean_object* v_a_1515_, lean_object* v_inst_1516_, lean_object* v_R_1517_, lean_object* v_a_1518_, lean_object* v_b_1519_, lean_object* v_c_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1511_, v_structName_1512_, v_e_1513_, v_idx_1514_, v_a_1515_, v_a_1518_, v_b_1519_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1527_, lean_object* v_structName_1528_, lean_object* v_e_1529_, lean_object* v_idx_1530_, lean_object* v_a_1531_, lean_object* v_inst_1532_, lean_object* v_R_1533_, lean_object* v_a_1534_, lean_object* v_b_1535_, lean_object* v_c_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1527_, v_structName_1528_, v_e_1529_, v_idx_1530_, v_a_1531_, v_inst_1532_, v_R_1533_, v_a_1534_, v_b_1535_, v_c_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_upperBound_1527_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1543_, lean_object* v_structName_1544_, lean_object* v_e_1545_, lean_object* v_idx_1546_, lean_object* v_a_1547_, lean_object* v_inst_1548_, lean_object* v_R_1549_, lean_object* v_a_1550_, lean_object* v_b_1551_, lean_object* v_c_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1543_, v_structName_1544_, v_e_1545_, v_idx_1546_, v_a_1547_, v_a_1550_, v_b_1551_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1559_, lean_object* v_structName_1560_, lean_object* v_e_1561_, lean_object* v_idx_1562_, lean_object* v_a_1563_, lean_object* v_inst_1564_, lean_object* v_R_1565_, lean_object* v_a_1566_, lean_object* v_b_1567_, lean_object* v_c_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1559_, v_structName_1560_, v_e_1561_, v_idx_1562_, v_a_1563_, v_inst_1564_, v_R_1565_, v_a_1566_, v_b_1567_, v_c_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v_upperBound_1559_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1577_ = l_Lean_stringToMessageData(v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1584_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1585_ = l_Lean_indentExpr(v_type_1578_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1586_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1595_, lean_object* v_type_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_type_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1603_, v_type_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v_ks_1615_; lean_object* v_vs_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1640_; 
v_ks_1615_ = lean_ctor_get(v_x_1611_, 0);
v_vs_1616_ = lean_ctor_get(v_x_1611_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_x_1611_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1618_ = v_x_1611_;
v_isShared_1619_ = v_isSharedCheck_1640_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_vs_1616_);
lean_inc(v_ks_1615_);
lean_dec(v_x_1611_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1640_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = lean_array_get_size(v_ks_1615_);
v___x_1621_ = lean_nat_dec_lt(v_x_1612_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec(v_x_1612_);
v___x_1622_ = lean_array_push(v_ks_1615_, v_x_1613_);
v___x_1623_ = lean_array_push(v_vs_1616_, v_x_1614_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___x_1623_);
lean_ctor_set(v___x_1618_, 0, v___x_1622_);
v___x_1625_ = v___x_1618_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v_k_x27_1627_; uint8_t v___x_1628_; 
v_k_x27_1627_ = lean_array_fget_borrowed(v_ks_1615_, v_x_1612_);
v___x_1628_ = l_Lean_instBEqMVarId_beq(v_x_1613_, v_k_x27_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1630_; 
if (v_isShared_1619_ == 0)
{
v___x_1630_ = v___x_1618_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_ks_1615_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_vs_1616_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_add(v_x_1612_, v___x_1631_);
lean_dec(v_x_1612_);
v_x_1611_ = v___x_1630_;
v_x_1612_ = v___x_1632_;
goto _start;
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1635_ = lean_array_fset(v_ks_1615_, v_x_1612_, v_x_1613_);
v___x_1636_ = lean_array_fset(v_vs_1616_, v_x_1612_, v_x_1614_);
lean_dec(v_x_1612_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___x_1636_);
lean_ctor_set(v___x_1618_, 0, v___x_1635_);
v___x_1638_ = v___x_1618_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1641_, lean_object* v_k_1642_, lean_object* v_v_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1641_, v___x_1644_, v_k_1642_, v_v_1643_);
return v___x_1645_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; 
v___x_1646_ = ((size_t)5ULL);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_shift_left(v___x_1647_, v___x_1646_);
return v___x_1648_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; 
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1651_ = lean_usize_sub(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1653_, size_t v_x_1654_, size_t v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1653_) == 0)
{
lean_object* v_es_1658_; size_t v___x_1659_; size_t v___x_1660_; size_t v___x_1661_; size_t v___x_1662_; lean_object* v_j_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_es_1658_ = lean_ctor_get(v_x_1653_, 0);
v___x_1659_ = ((size_t)5ULL);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1662_ = lean_usize_land(v_x_1654_, v___x_1661_);
v_j_1663_ = lean_usize_to_nat(v___x_1662_);
v___x_1664_ = lean_array_get_size(v_es_1658_);
v___x_1665_ = lean_nat_dec_lt(v_j_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec(v_j_1663_);
lean_dec(v_x_1657_);
lean_dec(v_x_1656_);
return v_x_1653_;
}
else
{
lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1702_; 
lean_inc_ref(v_es_1658_);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v_x_1653_, 0);
lean_dec(v_unused_1703_);
v___x_1667_ = v_x_1653_;
v_isShared_1668_ = v_isSharedCheck_1702_;
goto v_resetjp_1666_;
}
else
{
lean_dec(v_x_1653_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1702_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_v_1669_; lean_object* v___x_1670_; lean_object* v_xs_x27_1671_; lean_object* v___y_1673_; 
v_v_1669_ = lean_array_fget(v_es_1658_, v_j_1663_);
v___x_1670_ = lean_box(0);
v_xs_x27_1671_ = lean_array_fset(v_es_1658_, v_j_1663_, v___x_1670_);
switch(lean_obj_tag(v_v_1669_))
{
case 0:
{
lean_object* v_key_1678_; lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1689_; 
v_key_1678_ = lean_ctor_get(v_v_1669_, 0);
v_val_1679_ = lean_ctor_get(v_v_1669_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_v_1669_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1681_ = v_v_1669_;
v_isShared_1682_ = v_isSharedCheck_1689_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_inc(v_key_1678_);
lean_dec(v_v_1669_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1689_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
uint8_t v___x_1683_; 
v___x_1683_ = l_Lean_instBEqMVarId_beq(v_x_1656_, v_key_1678_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
lean_del_object(v___x_1681_);
v___x_1684_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1678_, v_val_1679_, v_x_1656_, v_x_1657_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
v___y_1673_ = v___x_1685_;
goto v___jp_1672_;
}
else
{
lean_object* v___x_1687_; 
lean_dec(v_val_1679_);
lean_dec(v_key_1678_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_x_1657_);
lean_ctor_set(v___x_1681_, 0, v_x_1656_);
v___x_1687_ = v___x_1681_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_x_1656_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_x_1657_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
v___y_1673_ = v___x_1687_;
goto v___jp_1672_;
}
}
}
}
case 1:
{
lean_object* v_node_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1700_; 
v_node_1690_ = lean_ctor_get(v_v_1669_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_v_1669_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1692_ = v_v_1669_;
v_isShared_1693_ = v_isSharedCheck_1700_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_node_1690_);
lean_dec(v_v_1669_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1700_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
size_t v___x_1694_; size_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1694_ = lean_usize_shift_right(v_x_1654_, v___x_1659_);
v___x_1695_ = lean_usize_add(v_x_1655_, v___x_1660_);
v___x_1696_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1690_, v___x_1694_, v___x_1695_, v_x_1656_, v_x_1657_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1696_);
v___x_1698_ = v___x_1692_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
v___y_1673_ = v___x_1698_;
goto v___jp_1672_;
}
}
}
default: 
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_x_1656_);
lean_ctor_set(v___x_1701_, 1, v_x_1657_);
v___y_1673_ = v___x_1701_;
goto v___jp_1672_;
}
}
v___jp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = lean_array_fset(v_xs_x27_1671_, v_j_1663_, v___y_1673_);
lean_dec(v_j_1663_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1674_);
v___x_1676_ = v___x_1667_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
else
{
lean_object* v_ks_1704_; lean_object* v_vs_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1725_; 
v_ks_1704_ = lean_ctor_get(v_x_1653_, 0);
v_vs_1705_ = lean_ctor_get(v_x_1653_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_x_1653_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1707_ = v_x_1653_;
v_isShared_1708_ = v_isSharedCheck_1725_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_vs_1705_);
lean_inc(v_ks_1704_);
lean_dec(v_x_1653_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1725_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_ks_1704_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_vs_1705_);
v___x_1710_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v_newNode_1711_; uint8_t v___y_1713_; size_t v___x_1719_; uint8_t v___x_1720_; 
v_newNode_1711_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1710_, v_x_1656_, v_x_1657_);
v___x_1719_ = ((size_t)7ULL);
v___x_1720_ = lean_usize_dec_le(v___x_1719_, v_x_1655_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1711_);
v___x_1722_ = lean_unsigned_to_nat(4u);
v___x_1723_ = lean_nat_dec_lt(v___x_1721_, v___x_1722_);
lean_dec(v___x_1721_);
v___y_1713_ = v___x_1723_;
goto v___jp_1712_;
}
else
{
v___y_1713_ = v___x_1720_;
goto v___jp_1712_;
}
v___jp_1712_:
{
if (v___y_1713_ == 0)
{
lean_object* v_ks_1714_; lean_object* v_vs_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_ks_1714_ = lean_ctor_get(v_newNode_1711_, 0);
lean_inc_ref(v_ks_1714_);
v_vs_1715_ = lean_ctor_get(v_newNode_1711_, 1);
lean_inc_ref(v_vs_1715_);
lean_dec_ref(v_newNode_1711_);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1655_, v_ks_1714_, v_vs_1715_, v___x_1716_, v___x_1717_);
lean_dec_ref(v_vs_1715_);
lean_dec_ref(v_ks_1714_);
return v___x_1718_;
}
else
{
return v_newNode_1711_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1726_, lean_object* v_keys_1727_, lean_object* v_vals_1728_, lean_object* v_i_1729_, lean_object* v_entries_1730_){
_start:
{
lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1731_ = lean_array_get_size(v_keys_1727_);
v___x_1732_ = lean_nat_dec_lt(v_i_1729_, v___x_1731_);
if (v___x_1732_ == 0)
{
lean_dec(v_i_1729_);
return v_entries_1730_;
}
else
{
lean_object* v_k_1733_; lean_object* v_v_1734_; uint64_t v___x_1735_; size_t v_h_1736_; size_t v___x_1737_; lean_object* v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; size_t v_h_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_k_1733_ = lean_array_fget_borrowed(v_keys_1727_, v_i_1729_);
v_v_1734_ = lean_array_fget_borrowed(v_vals_1728_, v_i_1729_);
v___x_1735_ = l_Lean_instHashableMVarId_hash(v_k_1733_);
v_h_1736_ = lean_uint64_to_usize(v___x_1735_);
v___x_1737_ = ((size_t)5ULL);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_sub(v_depth_1726_, v___x_1739_);
v___x_1741_ = lean_usize_mul(v___x_1737_, v___x_1740_);
v_h_1742_ = lean_usize_shift_right(v_h_1736_, v___x_1741_);
v___x_1743_ = lean_nat_add(v_i_1729_, v___x_1738_);
lean_dec(v_i_1729_);
lean_inc(v_v_1734_);
lean_inc(v_k_1733_);
v___x_1744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1730_, v_h_1742_, v_depth_1726_, v_k_1733_, v_v_1734_);
v_i_1729_ = v___x_1743_;
v_entries_1730_ = v___x_1744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1746_, lean_object* v_keys_1747_, lean_object* v_vals_1748_, lean_object* v_i_1749_, lean_object* v_entries_1750_){
_start:
{
size_t v_depth_boxed_1751_; lean_object* v_res_1752_; 
v_depth_boxed_1751_ = lean_unbox_usize(v_depth_1746_);
lean_dec(v_depth_1746_);
v_res_1752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1751_, v_keys_1747_, v_vals_1748_, v_i_1749_, v_entries_1750_);
lean_dec_ref(v_vals_1748_);
lean_dec_ref(v_keys_1747_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1753_, lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
size_t v_x_1244__boxed_1758_; size_t v_x_1245__boxed_1759_; lean_object* v_res_1760_; 
v_x_1244__boxed_1758_ = lean_unbox_usize(v_x_1754_);
lean_dec(v_x_1754_);
v_x_1245__boxed_1759_ = lean_unbox_usize(v_x_1755_);
lean_dec(v_x_1755_);
v_res_1760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1753_, v_x_1244__boxed_1758_, v_x_1245__boxed_1759_, v_x_1756_, v_x_1757_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
uint64_t v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
v___x_1764_ = l_Lean_instHashableMVarId_hash(v_x_1762_);
v___x_1765_ = lean_uint64_to_usize(v___x_1764_);
v___x_1766_ = ((size_t)1ULL);
v___x_1767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1761_, v___x_1765_, v___x_1766_, v_x_1762_, v_x_1763_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1768_, lean_object* v_val_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; lean_object* v_mctx_1773_; lean_object* v_cache_1774_; lean_object* v_zetaDeltaFVarIds_1775_; lean_object* v_postponed_1776_; lean_object* v_diag_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1805_; 
v___x_1772_ = lean_st_ref_take(v___y_1770_);
v_mctx_1773_ = lean_ctor_get(v___x_1772_, 0);
v_cache_1774_ = lean_ctor_get(v___x_1772_, 1);
v_zetaDeltaFVarIds_1775_ = lean_ctor_get(v___x_1772_, 2);
v_postponed_1776_ = lean_ctor_get(v___x_1772_, 3);
v_diag_1777_ = lean_ctor_get(v___x_1772_, 4);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1779_ = v___x_1772_;
v_isShared_1780_ = v_isSharedCheck_1805_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_diag_1777_);
lean_inc(v_postponed_1776_);
lean_inc(v_zetaDeltaFVarIds_1775_);
lean_inc(v_cache_1774_);
lean_inc(v_mctx_1773_);
lean_dec(v___x_1772_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1805_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_depth_1781_; lean_object* v_levelAssignDepth_1782_; lean_object* v_lmvarCounter_1783_; lean_object* v_mvarCounter_1784_; lean_object* v_lDecls_1785_; lean_object* v_decls_1786_; lean_object* v_userNames_1787_; lean_object* v_lAssignment_1788_; lean_object* v_eAssignment_1789_; lean_object* v_dAssignment_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1804_; 
v_depth_1781_ = lean_ctor_get(v_mctx_1773_, 0);
v_levelAssignDepth_1782_ = lean_ctor_get(v_mctx_1773_, 1);
v_lmvarCounter_1783_ = lean_ctor_get(v_mctx_1773_, 2);
v_mvarCounter_1784_ = lean_ctor_get(v_mctx_1773_, 3);
v_lDecls_1785_ = lean_ctor_get(v_mctx_1773_, 4);
v_decls_1786_ = lean_ctor_get(v_mctx_1773_, 5);
v_userNames_1787_ = lean_ctor_get(v_mctx_1773_, 6);
v_lAssignment_1788_ = lean_ctor_get(v_mctx_1773_, 7);
v_eAssignment_1789_ = lean_ctor_get(v_mctx_1773_, 8);
v_dAssignment_1790_ = lean_ctor_get(v_mctx_1773_, 9);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_mctx_1773_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1792_ = v_mctx_1773_;
v_isShared_1793_ = v_isSharedCheck_1804_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_dAssignment_1790_);
lean_inc(v_eAssignment_1789_);
lean_inc(v_lAssignment_1788_);
lean_inc(v_userNames_1787_);
lean_inc(v_decls_1786_);
lean_inc(v_lDecls_1785_);
lean_inc(v_mvarCounter_1784_);
lean_inc(v_lmvarCounter_1783_);
lean_inc(v_levelAssignDepth_1782_);
lean_inc(v_depth_1781_);
lean_dec(v_mctx_1773_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1804_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1794_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1789_, v_mvarId_1768_, v_val_1769_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 8, v___x_1794_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_depth_1781_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_levelAssignDepth_1782_);
lean_ctor_set(v_reuseFailAlloc_1803_, 2, v_lmvarCounter_1783_);
lean_ctor_set(v_reuseFailAlloc_1803_, 3, v_mvarCounter_1784_);
lean_ctor_set(v_reuseFailAlloc_1803_, 4, v_lDecls_1785_);
lean_ctor_set(v_reuseFailAlloc_1803_, 5, v_decls_1786_);
lean_ctor_set(v_reuseFailAlloc_1803_, 6, v_userNames_1787_);
lean_ctor_set(v_reuseFailAlloc_1803_, 7, v_lAssignment_1788_);
lean_ctor_set(v_reuseFailAlloc_1803_, 8, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1803_, 9, v_dAssignment_1790_);
v___x_1796_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1796_);
v___x_1798_ = v___x_1779_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_cache_1774_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_zetaDeltaFVarIds_1775_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_postponed_1776_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v_diag_1777_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_st_ref_set(v___y_1770_, v___x_1798_);
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1806_, lean_object* v_val_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1806_, v_val_1807_, v___y_1808_);
lean_dec(v___y_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1817_; 
lean_inc(v_a_1815_);
lean_inc_ref(v_a_1814_);
lean_inc(v_a_1813_);
lean_inc_ref(v_a_1812_);
lean_inc_ref(v_type_1811_);
v___x_1817_ = lean_infer_type(v_type_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = l_Lean_Meta_whnfD(v_a_1818_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1854_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1854_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1854_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
switch(lean_obj_tag(v_a_1820_))
{
case 3:
{
lean_object* v_u_1824_; lean_object* v___x_1826_; 
lean_dec_ref(v_type_1811_);
v_u_1824_ = lean_ctor_get(v_a_1820_, 0);
lean_inc(v_u_1824_);
lean_dec_ref(v_a_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_u_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_u_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
case 2:
{
lean_object* v_mvarId_1828_; lean_object* v___x_1829_; 
lean_del_object(v___x_1822_);
v_mvarId_1828_ = lean_ctor_get(v_a_1820_, 0);
lean_inc_n(v_mvarId_1828_, 2);
lean_dec_ref(v_a_1820_);
v___x_1829_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1828_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; uint8_t v___x_1831_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1829_);
v___x_1831_ = lean_unbox(v_a_1830_);
lean_dec(v_a_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec_ref(v_type_1811_);
v___x_1832_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc_n(v_a_1833_, 2);
lean_dec_ref(v___x_1832_);
v___x_1834_ = l_Lean_mkSort(v_a_1833_);
v___x_1835_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1828_, v___x_1834_, v_a_1813_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v___x_1835_, 0);
lean_dec(v_unused_1843_);
v___x_1837_ = v___x_1835_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_dec(v___x_1835_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v_a_1833_);
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1833_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_dec(v_mvarId_1828_);
return v___x_1832_;
}
}
else
{
lean_object* v___x_1844_; 
lean_dec(v_mvarId_1828_);
v___x_1844_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
return v___x_1844_;
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_mvarId_1828_);
lean_dec_ref(v_type_1811_);
v_a_1845_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1829_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1829_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
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
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
default: 
{
lean_object* v___x_1853_; 
lean_del_object(v___x_1822_);
lean_dec(v_a_1820_);
v___x_1853_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_type_1811_);
v_a_1855_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1819_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1819_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_type_1811_);
v_a_1863_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1817_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1817_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Meta_getLevel(v_type_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1878_, lean_object* v_val_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1878_, v_val_1879_, v___y_1881_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1886_, lean_object* v_val_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1886_, v_val_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1895_, v_x_1896_, v_x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1899_, lean_object* v_x_1900_, size_t v_x_1901_, size_t v_x_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1900_, v_x_1901_, v_x_1902_, v_x_1903_, v_x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
size_t v_x_1603__boxed_1912_; size_t v_x_1604__boxed_1913_; lean_object* v_res_1914_; 
v_x_1603__boxed_1912_ = lean_unbox_usize(v_x_1908_);
lean_dec(v_x_1908_);
v_x_1604__boxed_1913_ = lean_unbox_usize(v_x_1909_);
lean_dec(v_x_1909_);
v_res_1914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_1906_, v_x_1907_, v_x_1603__boxed_1912_, v_x_1604__boxed_1913_, v_x_1910_, v_x_1911_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1915_, lean_object* v_n_1916_, lean_object* v_k_1917_, lean_object* v_v_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1916_, v_k_1917_, v_v_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1920_, size_t v_depth_1921_, lean_object* v_keys_1922_, lean_object* v_vals_1923_, lean_object* v_heq_1924_, lean_object* v_i_1925_, lean_object* v_entries_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1921_, v_keys_1922_, v_vals_1923_, v_i_1925_, v_entries_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1928_, lean_object* v_depth_1929_, lean_object* v_keys_1930_, lean_object* v_vals_1931_, lean_object* v_heq_1932_, lean_object* v_i_1933_, lean_object* v_entries_1934_){
_start:
{
size_t v_depth_boxed_1935_; lean_object* v_res_1936_; 
v_depth_boxed_1935_ = lean_unbox_usize(v_depth_1929_);
lean_dec(v_depth_1929_);
v_res_1936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1928_, v_depth_boxed_1935_, v_keys_1930_, v_vals_1931_, v_heq_1932_, v_i_1933_, v_entries_1934_);
lean_dec_ref(v_vals_1931_);
lean_dec_ref(v_keys_1930_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_, lean_object* v_x_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1938_, v_x_1939_, v_x_1940_, v_x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_1943_, lean_object* v_b_1944_, lean_object* v_c_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
lean_inc(v___y_1949_);
lean_inc_ref(v___y_1948_);
lean_inc(v___y_1947_);
lean_inc_ref(v___y_1946_);
v___x_1951_ = lean_apply_7(v_k_1943_, v_b_1944_, v_c_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, lean_box(0));
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_1952_, lean_object* v_b_1953_, lean_object* v_c_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_1952_, v_b_1953_, v_c_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_1961_, lean_object* v_k_1962_, uint8_t v_cleanupAnnotations_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___f_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1969_, 0, v_k_1962_);
v___x_1970_ = 0;
v___x_1971_ = lean_box(0);
v___x_1972_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1970_, v___x_1971_, v_type_1961_, v___f_1969_, v_cleanupAnnotations_1963_, v___x_1970_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
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
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1972_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1972_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_1989_, lean_object* v_k_1990_, lean_object* v_cleanupAnnotations_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1997_; lean_object* v_res_1998_; 
v_cleanupAnnotations_boxed_1997_ = lean_unbox(v_cleanupAnnotations_1991_);
v_res_1998_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_1989_, v_k_1990_, v_cleanupAnnotations_boxed_1997_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_1999_, lean_object* v_type_2000_, lean_object* v_k_2001_, uint8_t v_cleanupAnnotations_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_2000_, v_k_2001_, v_cleanupAnnotations_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2009_, lean_object* v_type_2010_, lean_object* v_k_2011_, lean_object* v_cleanupAnnotations_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2018_; lean_object* v_res_2019_; 
v_cleanupAnnotations_boxed_2018_ = lean_unbox(v_cleanupAnnotations_2012_);
v_res_2019_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2009_, v_type_2010_, v_k_2011_, v_cleanupAnnotations_boxed_2018_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2020_, size_t v_i_2021_, size_t v_stop_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_usize_dec_eq(v_i_2021_, v_stop_2022_);
if (v___x_2029_ == 0)
{
size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_sub(v_i_2021_, v___x_2030_);
v___x_2032_ = lean_array_uget_borrowed(v_as_2020_, v___x_2031_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___x_2032_);
v___x_2033_ = lean_infer_type(v___x_2032_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_Meta_getLevel(v_a_2034_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref(v___x_2035_);
v___x_2037_ = l_Lean_mkLevelIMax_x27(v_a_2036_, v_b_2023_);
v_i_2021_ = v___x_2031_;
v_b_2023_ = v___x_2037_;
goto _start;
}
else
{
lean_dec(v_b_2023_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2035_);
v_i_2021_ = v___x_2031_;
v_b_2023_ = v_a_2039_;
goto _start;
}
else
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_b_2023_);
v_a_2041_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2033_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2033_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_b_2023_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2050_, lean_object* v_i_2051_, lean_object* v_stop_2052_, lean_object* v_b_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
size_t v_i_boxed_2059_; size_t v_stop_boxed_2060_; lean_object* v_res_2061_; 
v_i_boxed_2059_ = lean_unbox_usize(v_i_2051_);
lean_dec(v_i_2051_);
v_stop_boxed_2060_ = lean_unbox_usize(v_stop_2052_);
lean_dec(v_stop_2052_);
v_res_2061_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2050_, v_i_boxed_2059_, v_stop_boxed_2060_, v_b_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec_ref(v_as_2050_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2062_, lean_object* v_e_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___y_2070_; lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Meta_getLevel(v_e_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
v___x_2091_ = lean_array_get_size(v_xs_2062_);
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = lean_nat_dec_lt(v___x_2092_, v___x_2091_);
if (v___x_2093_ == 0)
{
lean_dec(v_a_2090_);
v___y_2070_ = v___x_2089_;
goto v___jp_2069_;
}
else
{
size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
lean_dec_ref(v___x_2089_);
v___x_2094_ = lean_usize_of_nat(v___x_2091_);
v___x_2095_ = ((size_t)0ULL);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2062_, v___x_2094_, v___x_2095_, v_a_2090_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
v___y_2070_ = v___x_2096_;
goto v___jp_2069_;
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2089_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2089_);
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
v___jp_2069_:
{
if (lean_obj_tag(v___y_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2080_; 
v_a_2071_ = lean_ctor_get(v___y_2070_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___y_2070_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2073_ = v___y_2070_;
v_isShared_2074_ = v_isSharedCheck_2080_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___y_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2080_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2075_ = l_Lean_Level_normalize(v_a_2071_);
lean_dec(v_a_2071_);
v___x_2076_ = l_Lean_mkSort(v___x_2075_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___y_2070_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___y_2070_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___y_2070_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___y_2070_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2105_, lean_object* v_e_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2105_, v_e_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec_ref(v_xs_2105_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___f_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; 
v___f_2120_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2121_ = 0;
v___x_2122_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2114_, v___f_2120_, v___x_2121_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2130_, lean_object* v_k_2131_, uint8_t v_cleanupAnnotations_2132_, uint8_t v_preserveNondepLet_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___f_2139_; uint8_t v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2139_, 0, v_k_2131_);
v___x_2140_ = 1;
v___x_2141_ = 0;
v___x_2142_ = lean_box(0);
v___x_2143_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2130_, v___x_2140_, v___x_2140_, v_preserveNondepLet_2133_, v___x_2141_, v___x_2142_, v___f_2139_, v_cleanupAnnotations_2132_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2143_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2143_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2160_, lean_object* v_k_2161_, lean_object* v_cleanupAnnotations_2162_, lean_object* v_preserveNondepLet_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2169_; uint8_t v_preserveNondepLet_boxed_2170_; lean_object* v_res_2171_; 
v_cleanupAnnotations_boxed_2169_ = lean_unbox(v_cleanupAnnotations_2162_);
v_preserveNondepLet_boxed_2170_ = lean_unbox(v_preserveNondepLet_2163_);
v_res_2171_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2160_, v_k_2161_, v_cleanupAnnotations_boxed_2169_, v_preserveNondepLet_boxed_2170_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2172_, lean_object* v_e_2173_, lean_object* v_k_2174_, uint8_t v_cleanupAnnotations_2175_, uint8_t v_preserveNondepLet_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2173_, v_k_2174_, v_cleanupAnnotations_2175_, v_preserveNondepLet_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_e_2184_, lean_object* v_k_2185_, lean_object* v_cleanupAnnotations_2186_, lean_object* v_preserveNondepLet_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2193_; uint8_t v_preserveNondepLet_boxed_2194_; lean_object* v_res_2195_; 
v_cleanupAnnotations_boxed_2193_ = lean_unbox(v_cleanupAnnotations_2186_);
v_preserveNondepLet_boxed_2194_ = lean_unbox(v_preserveNondepLet_2187_);
v_res_2195_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2183_, v_e_2184_, v_k_2185_, v_cleanupAnnotations_boxed_2193_, v_preserveNondepLet_boxed_2194_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2196_, lean_object* v_e_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
v___x_2203_ = lean_infer_type(v_e_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; uint8_t v___x_2205_; uint8_t v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = 0;
v___x_2206_ = 1;
v___x_2207_ = 1;
v___x_2208_ = l_Lean_Meta_mkForallFVars(v_xs_2196_, v_a_2204_, v___x_2205_, v___x_2206_, v___x_2205_, v___x_2207_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
return v___x_2208_;
}
else
{
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2209_, lean_object* v_e_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2209_, v_e_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec_ref(v_xs_2209_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___f_2224_; uint8_t v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; 
v___f_2224_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2225_ = 0;
v___x_2226_ = 1;
v___x_2227_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2218_, v___f_2224_, v___x_2225_, v___x_2226_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
return v_res_2234_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2247_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2248_ = l_Lean_MessageData_ofName(v_mvarId_2241_);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2251_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2260_, lean_object* v_mvarId_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_mvarId_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2268_, v_mvarId_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; lean_object* v_mctx_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_st_ref_get(v_a_2278_);
v_mctx_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc_ref(v_mctx_2283_);
lean_dec(v___x_2282_);
v___x_2284_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2283_, v_mvarId_2276_);
lean_dec_ref(v_mctx_2283_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2285_;
}
else
{
lean_object* v_val_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_mvarId_2276_);
v_val_2286_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2288_ = v___x_2284_;
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_val_2286_);
lean_dec(v___x_2284_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_type_2290_; lean_object* v___x_2292_; 
v_type_2290_ = lean_ctor_get(v_val_2286_, 2);
lean_inc_ref(v_type_2290_);
lean_dec(v_val_2286_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set_tag(v___x_2288_, 0);
lean_ctor_set(v___x_2288_, 0, v_type_2290_);
v___x_2292_ = v___x_2288_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_type_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_lctx_2307_; lean_object* v___x_2308_; 
v_lctx_2307_ = lean_ctor_get(v_a_2303_, 2);
lean_inc(v_fvarId_2302_);
lean_inc_ref(v_lctx_2307_);
v___x_2308_ = lean_local_ctx_find(v_lctx_2307_, v_fvarId_2302_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2302_, v_a_2304_, v_a_2305_);
return v___x_2309_;
}
else
{
lean_object* v_val_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v_fvarId_2302_);
v_val_2310_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2312_ = v___x_2308_;
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_val_2310_);
lean_dec(v___x_2308_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = l_Lean_LocalDecl_type(v_val_2310_);
lean_dec(v_val_2310_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set_tag(v___x_2312_, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2314_);
v___x_2316_ = v___x_2312_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec_ref(v_a_2320_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2325_, v_a_2326_, v_a_2328_, v_a_2329_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
return v_res_2338_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0(void){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_instMonadEIO(lean_box(0));
return v___x_2339_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
v___x_2341_ = l_StateRefT_x27_instMonad___redArg(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4(void){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2344_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___f_2346_; 
v___x_2345_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2346_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2346_, 0, v___x_2345_);
return v___f_2346_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___f_2348_; 
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__4);
v___f_2348_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2348_, 0, v___x_2347_);
return v___f_2348_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7(void){
_start:
{
lean_object* v___f_2349_; lean_object* v___f_2350_; lean_object* v___x_2351_; 
v___f_2349_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__6);
v___f_2350_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__5);
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___f_2350_);
lean_ctor_set(v___x_2351_, 1, v___f_2349_);
return v___x_2351_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___f_2353_; 
v___x_2352_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2353_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2353_, 0, v___x_2352_);
return v___f_2353_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___f_2355_; 
v___x_2354_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__7);
v___f_2355_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2355_, 0, v___x_2354_);
return v___f_2355_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10(void){
_start:
{
lean_object* v___f_2356_; lean_object* v___f_2357_; lean_object* v___x_2358_; 
v___f_2356_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__9);
v___f_2357_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__8);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___f_2357_);
lean_ctor_set(v___x_2358_, 1, v___f_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2361_, lean_object* v_inferType_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
uint8_t v_cacheInferType_2406_; 
v_cacheInferType_2406_ = lean_ctor_get_uint8(v_a_2363_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2406_ == 0)
{
lean_dec_ref(v_e_2361_);
goto v___jp_2368_;
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = l_Lean_Expr_hasMVar(v_e_2361_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2361_, v_a_2363_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2509_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2509_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2509_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2455_; lean_object* v_cache_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2504_; 
v___x_2455_ = lean_st_ref_get(v_a_2364_);
v_cache_2456_ = lean_ctor_get(v___x_2455_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; 
v_unused_2505_ = lean_ctor_get(v___x_2455_, 4);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v___x_2455_, 3);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v___x_2455_, 2);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2508_);
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2504_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_cache_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2504_;
goto v_resetjp_2457_;
}
v___jp_2413_:
{
lean_object* v___x_2414_; 
lean_inc(v_a_2366_);
lean_inc_ref(v_a_2365_);
lean_inc(v_a_2364_);
lean_inc_ref(v_a_2363_);
v___x_2414_ = lean_apply_5(v_inferType_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, lean_box(0));
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; uint8_t v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
v___x_2416_ = l_Lean_Expr_hasMVar(v_a_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2453_; 
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v___x_2414_, 0);
lean_dec(v_unused_2454_);
v___x_2418_ = v___x_2414_;
v_isShared_2419_ = v_isSharedCheck_2453_;
goto v_resetjp_2417_;
}
else
{
lean_dec(v___x_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2453_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v_cache_2421_; lean_object* v_mctx_2422_; lean_object* v_zetaDeltaFVarIds_2423_; lean_object* v_postponed_2424_; lean_object* v_diag_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2452_; 
v___x_2420_ = lean_st_ref_take(v_a_2364_);
v_cache_2421_ = lean_ctor_get(v___x_2420_, 1);
v_mctx_2422_ = lean_ctor_get(v___x_2420_, 0);
v_zetaDeltaFVarIds_2423_ = lean_ctor_get(v___x_2420_, 2);
v_postponed_2424_ = lean_ctor_get(v___x_2420_, 3);
v_diag_2425_ = lean_ctor_get(v___x_2420_, 4);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2427_ = v___x_2420_;
v_isShared_2428_ = v_isSharedCheck_2452_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_diag_2425_);
lean_inc(v_postponed_2424_);
lean_inc(v_zetaDeltaFVarIds_2423_);
lean_inc(v_cache_2421_);
lean_inc(v_mctx_2422_);
lean_dec(v___x_2420_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2452_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_inferType_2429_; lean_object* v_funInfo_2430_; lean_object* v_synthInstance_2431_; lean_object* v_whnf_2432_; lean_object* v_defEqTrans_2433_; lean_object* v_defEqPerm_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2451_; 
v_inferType_2429_ = lean_ctor_get(v_cache_2421_, 0);
v_funInfo_2430_ = lean_ctor_get(v_cache_2421_, 1);
v_synthInstance_2431_ = lean_ctor_get(v_cache_2421_, 2);
v_whnf_2432_ = lean_ctor_get(v_cache_2421_, 3);
v_defEqTrans_2433_ = lean_ctor_get(v_cache_2421_, 4);
v_defEqPerm_2434_ = lean_ctor_get(v_cache_2421_, 5);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_cache_2421_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2436_ = v_cache_2421_;
v_isShared_2437_ = v_isSharedCheck_2451_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_defEqPerm_2434_);
lean_inc(v_defEqTrans_2433_);
lean_inc(v_whnf_2432_);
lean_inc(v_synthInstance_2431_);
lean_inc(v_funInfo_2430_);
lean_inc(v_inferType_2429_);
lean_dec(v_cache_2421_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2451_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___f_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___f_2438_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2415_);
v___x_2440_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2438_, v___x_2439_, v_inferType_2429_, v_a_2409_, v_a_2415_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2440_);
v___x_2442_ = v___x_2436_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_funInfo_2430_);
lean_ctor_set(v_reuseFailAlloc_2450_, 2, v_synthInstance_2431_);
lean_ctor_set(v_reuseFailAlloc_2450_, 3, v_whnf_2432_);
lean_ctor_set(v_reuseFailAlloc_2450_, 4, v_defEqTrans_2433_);
lean_ctor_set(v_reuseFailAlloc_2450_, 5, v_defEqPerm_2434_);
v___x_2442_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2444_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v___x_2442_);
v___x_2444_ = v___x_2427_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_mctx_2422_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_zetaDeltaFVarIds_2423_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_postponed_2424_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_diag_2425_);
v___x_2444_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = lean_st_ref_set(v_a_2364_, v___x_2444_);
if (v_isShared_2419_ == 0)
{
v___x_2447_ = v___x_2418_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2415_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2415_);
lean_dec(v_a_2409_);
return v___x_2414_;
}
}
else
{
lean_dec(v_a_2409_);
return v___x_2414_;
}
}
v_resetjp_2457_:
{
lean_object* v_inferType_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_inferType_2460_ = lean_ctor_get(v_cache_2456_, 0);
lean_inc_ref(v_inferType_2460_);
lean_dec_ref(v_cache_2456_);
v___f_2461_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__11));
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__12));
lean_inc(v_a_2409_);
v___x_2463_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2461_, v___x_2462_, v_inferType_2460_, v_a_2409_);
lean_dec_ref(v_inferType_2460_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v___x_2464_; lean_object* v_toApplicative_2465_; lean_object* v_toFunctor_2466_; lean_object* v_toSeq_2467_; lean_object* v_toSeqLeft_2468_; lean_object* v_toSeqRight_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___f_2475_; lean_object* v___f_2476_; lean_object* v___f_2477_; lean_object* v___x_2479_; 
lean_del_object(v___x_2411_);
v___x_2464_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2465_ = lean_ctor_get(v___x_2464_, 0);
v_toFunctor_2466_ = lean_ctor_get(v_toApplicative_2465_, 0);
v_toSeq_2467_ = lean_ctor_get(v_toApplicative_2465_, 2);
v_toSeqLeft_2468_ = lean_ctor_get(v_toApplicative_2465_, 3);
v_toSeqRight_2469_ = lean_ctor_get(v_toApplicative_2465_, 4);
v___f_2470_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2471_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2466_, 2);
v___f_2472_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2472_, 0, v_toFunctor_2466_);
v___f_2473_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2473_, 0, v_toFunctor_2466_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___f_2472_);
lean_ctor_set(v___x_2474_, 1, v___f_2473_);
lean_inc(v_toSeqRight_2469_);
v___f_2475_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2475_, 0, v_toSeqRight_2469_);
lean_inc(v_toSeqLeft_2468_);
v___f_2476_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2476_, 0, v_toSeqLeft_2468_);
lean_inc(v_toSeq_2467_);
v___f_2477_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2477_, 0, v_toSeq_2467_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 4, v___f_2475_);
lean_ctor_set(v___x_2458_, 3, v___f_2476_);
lean_ctor_set(v___x_2458_, 2, v___f_2477_);
lean_ctor_set(v___x_2458_, 1, v___f_2470_);
lean_ctor_set(v___x_2458_, 0, v___x_2474_);
v___x_2479_ = v___x_2458_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___f_2470_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v___f_2477_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v___f_2476_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v___f_2475_);
v___x_2479_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v_cancelTk_x3f_2481_; 
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___f_2471_);
v_cancelTk_x3f_2481_ = lean_ctor_get(v_a_2365_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2481_) == 1)
{
lean_object* v_val_2482_; uint8_t v___x_2483_; 
v_val_2482_ = lean_ctor_get(v_cancelTk_x3f_2481_, 0);
v___x_2483_ = l_IO_CancelToken_isSet(v_val_2482_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v___x_2480_);
goto v___jp_2413_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2392__overap_2489_; lean_object* v___x_2490_; 
v___x_2484_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2485_ = l_Lean_Core_instMonadRefCoreM;
v___x_2486_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2487_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2486_, v___x_2480_);
v___x_2488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2484_);
lean_ctor_set(v___x_2488_, 1, v___x_2485_);
lean_ctor_set(v___x_2488_, 2, v___x_2487_);
v___x_2392__overap_2489_ = l_Lean_throwInterruptException___redArg(v___x_2488_);
lean_inc(v_a_2366_);
lean_inc_ref(v_a_2365_);
v___x_2490_ = lean_apply_3(v___x_2392__overap_2489_, v_a_2365_, v_a_2366_, lean_box(0));
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_dec_ref(v___x_2490_);
goto v___jp_2413_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v_a_2409_);
lean_dec_ref(v_inferType_2362_);
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2480_);
goto v___jp_2413_;
}
}
}
else
{
lean_object* v_val_2500_; lean_object* v___x_2502_; 
lean_del_object(v___x_2458_);
lean_dec(v_a_2409_);
lean_dec_ref(v_inferType_2362_);
v_val_2500_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_val_2500_);
lean_dec_ref(v___x_2463_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v_val_2500_);
v___x_2502_ = v___x_2411_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_val_2500_);
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
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref(v_inferType_2362_);
v_a_2510_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2408_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2408_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_dec_ref(v_e_2361_);
goto v___jp_2368_;
}
}
v___jp_2368_:
{
lean_object* v___x_2369_; lean_object* v_toApplicative_2370_; lean_object* v_toFunctor_2371_; lean_object* v_toSeq_2372_; lean_object* v_toSeqLeft_2373_; lean_object* v_toSeqRight_2374_; lean_object* v___f_2375_; lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___f_2378_; lean_object* v___x_2379_; lean_object* v___f_2380_; lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_cancelTk_x3f_2385_; 
v___x_2369_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
v_toApplicative_2370_ = lean_ctor_get(v___x_2369_, 0);
v_toFunctor_2371_ = lean_ctor_get(v_toApplicative_2370_, 0);
v_toSeq_2372_ = lean_ctor_get(v_toApplicative_2370_, 2);
v_toSeqLeft_2373_ = lean_ctor_get(v_toApplicative_2370_, 3);
v_toSeqRight_2374_ = lean_ctor_get(v_toApplicative_2370_, 4);
v___f_2375_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2));
v___f_2376_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3));
lean_inc_ref_n(v_toFunctor_2371_, 2);
v___f_2377_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2377_, 0, v_toFunctor_2371_);
v___f_2378_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2378_, 0, v_toFunctor_2371_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___f_2377_);
lean_ctor_set(v___x_2379_, 1, v___f_2378_);
lean_inc(v_toSeqRight_2374_);
v___f_2380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2380_, 0, v_toSeqRight_2374_);
lean_inc(v_toSeqLeft_2373_);
v___f_2381_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2381_, 0, v_toSeqLeft_2373_);
lean_inc(v_toSeq_2372_);
v___f_2382_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2382_, 0, v_toSeq_2372_);
v___x_2383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2379_);
lean_ctor_set(v___x_2383_, 1, v___f_2375_);
lean_ctor_set(v___x_2383_, 2, v___f_2382_);
lean_ctor_set(v___x_2383_, 3, v___f_2381_);
lean_ctor_set(v___x_2383_, 4, v___f_2380_);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v___f_2376_);
v_cancelTk_x3f_2385_ = lean_ctor_get(v_a_2365_, 12);
if (lean_obj_tag(v_cancelTk_x3f_2385_) == 1)
{
lean_object* v_val_2386_; uint8_t v___x_2387_; 
v_val_2386_ = lean_ctor_get(v_cancelTk_x3f_2385_, 0);
v___x_2387_ = l_IO_CancelToken_isSet(v_val_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; 
lean_dec_ref(v___x_2384_);
lean_inc(v_a_2366_);
lean_inc_ref(v_a_2365_);
lean_inc(v_a_2364_);
lean_inc_ref(v_a_2363_);
v___x_2388_ = lean_apply_5(v_inferType_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, lean_box(0));
return v___x_2388_;
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2189__overap_2394_; lean_object* v___x_2395_; 
v___x_2389_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10, &l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__10);
v___x_2390_ = l_Lean_Core_instMonadRefCoreM;
v___x_2391_ = l_Lean_Core_instAddMessageContextCoreM;
v___x_2392_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_2391_, v___x_2384_);
v___x_2393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2389_);
lean_ctor_set(v___x_2393_, 1, v___x_2390_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
v___x_2189__overap_2394_ = l_Lean_throwInterruptException___redArg(v___x_2393_);
lean_inc(v_a_2366_);
lean_inc_ref(v_a_2365_);
v___x_2395_ = lean_apply_3(v___x_2189__overap_2394_, v_a_2365_, v_a_2366_, lean_box(0));
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2396_; 
lean_dec_ref(v___x_2395_);
lean_inc(v_a_2366_);
lean_inc_ref(v_a_2365_);
lean_inc(v_a_2364_);
lean_inc_ref(v_a_2363_);
v___x_2396_ = lean_apply_5(v_inferType_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, lean_box(0));
return v___x_2396_;
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_inferType_2362_);
v_a_2397_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2395_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
else
{
lean_object* v___x_2405_; 
lean_dec_ref(v___x_2384_);
lean_inc(v_a_2366_);
lean_inc_ref(v_a_2365_);
lean_inc(v_a_2364_);
lean_inc_ref(v_a_2363_);
v___x_2405_ = lean_apply_5(v_inferType_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, lean_box(0));
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2518_, lean_object* v_inferType_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2518_, v_inferType_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v___y_2533_; uint8_t v___y_2534_; lean_object* v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; uint8_t v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___y_2543_; uint8_t v___y_2572_; lean_object* v___x_2630_; uint8_t v_transparency_2631_; uint8_t v___x_2632_; uint8_t v___x_2633_; 
v___x_2630_ = l_Lean_Meta_Context_config(v_a_2527_);
v_transparency_2631_ = lean_ctor_get_uint8(v___x_2630_, 9);
lean_dec_ref(v___x_2630_);
v___x_2632_ = 1;
v___x_2633_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
v___y_2572_ = v_transparency_2631_;
goto v___jp_2571_;
}
else
{
v___y_2572_ = v___x_2632_;
goto v___jp_2571_;
}
v___jp_2532_:
{
lean_object* v___x_2544_; uint8_t v_foApprox_2545_; uint8_t v_ctxApprox_2546_; uint8_t v_quasiPatternApprox_2547_; uint8_t v_constApprox_2548_; uint8_t v_isDefEqStuckEx_2549_; uint8_t v_unificationHints_2550_; uint8_t v_proofIrrelevance_2551_; uint8_t v_assignSyntheticOpaque_2552_; uint8_t v_offsetCnstrs_2553_; uint8_t v_transparency_2554_; uint8_t v_univApprox_2555_; uint8_t v_zetaUnused_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2570_; 
v___x_2544_ = l_Lean_Meta_Context_config(v___y_2542_);
lean_dec_ref(v___y_2542_);
v_foApprox_2545_ = lean_ctor_get_uint8(v___x_2544_, 0);
v_ctxApprox_2546_ = lean_ctor_get_uint8(v___x_2544_, 1);
v_quasiPatternApprox_2547_ = lean_ctor_get_uint8(v___x_2544_, 2);
v_constApprox_2548_ = lean_ctor_get_uint8(v___x_2544_, 3);
v_isDefEqStuckEx_2549_ = lean_ctor_get_uint8(v___x_2544_, 4);
v_unificationHints_2550_ = lean_ctor_get_uint8(v___x_2544_, 5);
v_proofIrrelevance_2551_ = lean_ctor_get_uint8(v___x_2544_, 6);
v_assignSyntheticOpaque_2552_ = lean_ctor_get_uint8(v___x_2544_, 7);
v_offsetCnstrs_2553_ = lean_ctor_get_uint8(v___x_2544_, 8);
v_transparency_2554_ = lean_ctor_get_uint8(v___x_2544_, 9);
v_univApprox_2555_ = lean_ctor_get_uint8(v___x_2544_, 11);
v_zetaUnused_2556_ = lean_ctor_get_uint8(v___x_2544_, 17);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2558_ = v___x_2544_;
v_isShared_2559_ = v_isSharedCheck_2570_;
goto v_resetjp_2557_;
}
else
{
lean_dec(v___x_2544_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2570_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
uint8_t v___x_2560_; uint8_t v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2564_; 
v___x_2560_ = 1;
v___x_2561_ = 0;
v___x_2562_ = 2;
if (v_isShared_2559_ == 0)
{
v___x_2564_ = v___x_2558_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 0, v_foApprox_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 1, v_ctxApprox_2546_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 2, v_quasiPatternApprox_2547_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 3, v_constApprox_2548_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 4, v_isDefEqStuckEx_2549_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 5, v_unificationHints_2550_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 6, v_proofIrrelevance_2551_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 7, v_assignSyntheticOpaque_2552_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 8, v_offsetCnstrs_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 9, v_transparency_2554_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 11, v_univApprox_2555_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, 17, v_zetaUnused_2556_);
v___x_2564_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
uint64_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_ctor_set_uint8(v___x_2564_, 10, v___x_2561_);
lean_ctor_set_uint8(v___x_2564_, 12, v___x_2560_);
lean_ctor_set_uint8(v___x_2564_, 13, v___x_2560_);
lean_ctor_set_uint8(v___x_2564_, 14, v___x_2562_);
lean_ctor_set_uint8(v___x_2564_, 15, v___x_2560_);
lean_ctor_set_uint8(v___x_2564_, 16, v___x_2560_);
lean_ctor_set_uint8(v___x_2564_, 18, v___x_2560_);
v___x_2565_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2564_);
v___x_2566_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set_uint64(v___x_2566_, sizeof(void*)*1, v___x_2565_);
lean_inc(v___y_2535_);
lean_inc(v___y_2538_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2540_);
lean_inc_ref(v___y_2541_);
lean_inc(v___y_2533_);
v___x_2567_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___y_2533_);
lean_ctor_set(v___x_2567_, 2, v___y_2541_);
lean_ctor_set(v___x_2567_, 3, v___y_2540_);
lean_ctor_set(v___x_2567_, 4, v___y_2537_);
lean_ctor_set(v___x_2567_, 5, v___y_2538_);
lean_ctor_set(v___x_2567_, 6, v___y_2535_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*7, v___y_2539_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*7 + 1, v___y_2536_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*7 + 2, v___y_2534_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*7 + 3, v___y_2543_);
lean_inc(v_a_2530_);
lean_inc_ref(v_a_2529_);
lean_inc(v_a_2528_);
v___x_2568_ = lean_apply_5(v_x_2526_, v___x_2567_, v_a_2528_, v_a_2529_, v_a_2530_, lean_box(0));
return v___x_2568_;
}
}
}
v___jp_2571_:
{
lean_object* v___x_2573_; uint8_t v_foApprox_2574_; uint8_t v_ctxApprox_2575_; uint8_t v_quasiPatternApprox_2576_; uint8_t v_constApprox_2577_; uint8_t v_isDefEqStuckEx_2578_; uint8_t v_unificationHints_2579_; uint8_t v_proofIrrelevance_2580_; uint8_t v_assignSyntheticOpaque_2581_; uint8_t v_offsetCnstrs_2582_; uint8_t v_etaStruct_2583_; uint8_t v_univApprox_2584_; uint8_t v_iota_2585_; uint8_t v_beta_2586_; uint8_t v_proj_2587_; uint8_t v_zeta_2588_; uint8_t v_zetaDelta_2589_; uint8_t v_zetaUnused_2590_; uint8_t v_zetaHave_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2629_; 
v___x_2573_ = l_Lean_Meta_Context_config(v_a_2527_);
v_foApprox_2574_ = lean_ctor_get_uint8(v___x_2573_, 0);
v_ctxApprox_2575_ = lean_ctor_get_uint8(v___x_2573_, 1);
v_quasiPatternApprox_2576_ = lean_ctor_get_uint8(v___x_2573_, 2);
v_constApprox_2577_ = lean_ctor_get_uint8(v___x_2573_, 3);
v_isDefEqStuckEx_2578_ = lean_ctor_get_uint8(v___x_2573_, 4);
v_unificationHints_2579_ = lean_ctor_get_uint8(v___x_2573_, 5);
v_proofIrrelevance_2580_ = lean_ctor_get_uint8(v___x_2573_, 6);
v_assignSyntheticOpaque_2581_ = lean_ctor_get_uint8(v___x_2573_, 7);
v_offsetCnstrs_2582_ = lean_ctor_get_uint8(v___x_2573_, 8);
v_etaStruct_2583_ = lean_ctor_get_uint8(v___x_2573_, 10);
v_univApprox_2584_ = lean_ctor_get_uint8(v___x_2573_, 11);
v_iota_2585_ = lean_ctor_get_uint8(v___x_2573_, 12);
v_beta_2586_ = lean_ctor_get_uint8(v___x_2573_, 13);
v_proj_2587_ = lean_ctor_get_uint8(v___x_2573_, 14);
v_zeta_2588_ = lean_ctor_get_uint8(v___x_2573_, 15);
v_zetaDelta_2589_ = lean_ctor_get_uint8(v___x_2573_, 16);
v_zetaUnused_2590_ = lean_ctor_get_uint8(v___x_2573_, 17);
v_zetaHave_2591_ = lean_ctor_get_uint8(v___x_2573_, 18);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2593_ = v___x_2573_;
v_isShared_2594_ = v_isSharedCheck_2629_;
goto v_resetjp_2592_;
}
else
{
lean_dec(v___x_2573_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2629_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
uint8_t v_trackZetaDelta_2595_; lean_object* v_zetaDeltaSet_2596_; lean_object* v_lctx_2597_; lean_object* v_localInstances_2598_; lean_object* v_defEqCtx_x3f_2599_; lean_object* v_synthPendingDepth_2600_; lean_object* v_canUnfold_x3f_2601_; uint8_t v_univApprox_2602_; uint8_t v_inTypeClassResolution_2603_; uint8_t v_cacheInferType_2604_; lean_object* v_config_2606_; 
v_trackZetaDelta_2595_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7);
v_zetaDeltaSet_2596_ = lean_ctor_get(v_a_2527_, 1);
v_lctx_2597_ = lean_ctor_get(v_a_2527_, 2);
v_localInstances_2598_ = lean_ctor_get(v_a_2527_, 3);
v_defEqCtx_x3f_2599_ = lean_ctor_get(v_a_2527_, 4);
v_synthPendingDepth_2600_ = lean_ctor_get(v_a_2527_, 5);
v_canUnfold_x3f_2601_ = lean_ctor_get(v_a_2527_, 6);
v_univApprox_2602_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2603_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7 + 2);
v_cacheInferType_2604_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*7 + 3);
if (v_isShared_2594_ == 0)
{
v_config_2606_ = v___x_2593_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 0, v_foApprox_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 1, v_ctxApprox_2575_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 2, v_quasiPatternApprox_2576_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 3, v_constApprox_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 4, v_isDefEqStuckEx_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 5, v_unificationHints_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 6, v_proofIrrelevance_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 7, v_assignSyntheticOpaque_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 8, v_offsetCnstrs_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 10, v_etaStruct_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 11, v_univApprox_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 12, v_iota_2585_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 13, v_beta_2586_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 14, v_proj_2587_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 15, v_zeta_2588_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 16, v_zetaDelta_2589_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 17, v_zetaUnused_2590_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 18, v_zetaHave_2591_);
v_config_2606_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
uint64_t v___x_2607_; uint64_t v___x_2608_; uint64_t v___x_2609_; uint64_t v___x_2610_; uint64_t v___x_2611_; uint64_t v_key_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v_beta_2616_; 
lean_ctor_set_uint8(v_config_2606_, 9, v___y_2572_);
v___x_2607_ = l_Lean_Meta_Context_configKey(v_a_2527_);
v___x_2608_ = 2ULL;
v___x_2609_ = lean_uint64_shift_right(v___x_2607_, v___x_2608_);
v___x_2610_ = lean_uint64_shift_left(v___x_2609_, v___x_2608_);
v___x_2611_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2572_);
v_key_2612_ = lean_uint64_lor(v___x_2610_, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2613_, 0, v_config_2606_);
lean_ctor_set_uint64(v___x_2613_, sizeof(void*)*1, v_key_2612_);
lean_inc(v_canUnfold_x3f_2601_);
lean_inc(v_synthPendingDepth_2600_);
lean_inc(v_defEqCtx_x3f_2599_);
lean_inc_ref(v_localInstances_2598_);
lean_inc_ref(v_lctx_2597_);
lean_inc(v_zetaDeltaSet_2596_);
v___x_2614_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v_zetaDeltaSet_2596_);
lean_ctor_set(v___x_2614_, 2, v_lctx_2597_);
lean_ctor_set(v___x_2614_, 3, v_localInstances_2598_);
lean_ctor_set(v___x_2614_, 4, v_defEqCtx_x3f_2599_);
lean_ctor_set(v___x_2614_, 5, v_synthPendingDepth_2600_);
lean_ctor_set(v___x_2614_, 6, v_canUnfold_x3f_2601_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*7, v_trackZetaDelta_2595_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*7 + 1, v_univApprox_2602_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2603_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*7 + 3, v_cacheInferType_2604_);
v___x_2615_ = l_Lean_Meta_Context_config(v___x_2614_);
v_beta_2616_ = lean_ctor_get_uint8(v___x_2615_, 13);
if (v_beta_2616_ == 0)
{
lean_dec_ref(v___x_2615_);
v___y_2533_ = v_zetaDeltaSet_2596_;
v___y_2534_ = v_inTypeClassResolution_2603_;
v___y_2535_ = v_canUnfold_x3f_2601_;
v___y_2536_ = v_univApprox_2602_;
v___y_2537_ = v_defEqCtx_x3f_2599_;
v___y_2538_ = v_synthPendingDepth_2600_;
v___y_2539_ = v_trackZetaDelta_2595_;
v___y_2540_ = v_localInstances_2598_;
v___y_2541_ = v_lctx_2597_;
v___y_2542_ = v___x_2614_;
v___y_2543_ = v_cacheInferType_2604_;
goto v___jp_2532_;
}
else
{
uint8_t v_iota_2617_; 
v_iota_2617_ = lean_ctor_get_uint8(v___x_2615_, 12);
if (v_iota_2617_ == 0)
{
lean_dec_ref(v___x_2615_);
v___y_2533_ = v_zetaDeltaSet_2596_;
v___y_2534_ = v_inTypeClassResolution_2603_;
v___y_2535_ = v_canUnfold_x3f_2601_;
v___y_2536_ = v_univApprox_2602_;
v___y_2537_ = v_defEqCtx_x3f_2599_;
v___y_2538_ = v_synthPendingDepth_2600_;
v___y_2539_ = v_trackZetaDelta_2595_;
v___y_2540_ = v_localInstances_2598_;
v___y_2541_ = v_lctx_2597_;
v___y_2542_ = v___x_2614_;
v___y_2543_ = v_cacheInferType_2604_;
goto v___jp_2532_;
}
else
{
uint8_t v_zeta_2618_; 
v_zeta_2618_ = lean_ctor_get_uint8(v___x_2615_, 15);
if (v_zeta_2618_ == 0)
{
lean_dec_ref(v___x_2615_);
v___y_2533_ = v_zetaDeltaSet_2596_;
v___y_2534_ = v_inTypeClassResolution_2603_;
v___y_2535_ = v_canUnfold_x3f_2601_;
v___y_2536_ = v_univApprox_2602_;
v___y_2537_ = v_defEqCtx_x3f_2599_;
v___y_2538_ = v_synthPendingDepth_2600_;
v___y_2539_ = v_trackZetaDelta_2595_;
v___y_2540_ = v_localInstances_2598_;
v___y_2541_ = v_lctx_2597_;
v___y_2542_ = v___x_2614_;
v___y_2543_ = v_cacheInferType_2604_;
goto v___jp_2532_;
}
else
{
uint8_t v_zetaHave_2619_; 
v_zetaHave_2619_ = lean_ctor_get_uint8(v___x_2615_, 18);
if (v_zetaHave_2619_ == 0)
{
lean_dec_ref(v___x_2615_);
v___y_2533_ = v_zetaDeltaSet_2596_;
v___y_2534_ = v_inTypeClassResolution_2603_;
v___y_2535_ = v_canUnfold_x3f_2601_;
v___y_2536_ = v_univApprox_2602_;
v___y_2537_ = v_defEqCtx_x3f_2599_;
v___y_2538_ = v_synthPendingDepth_2600_;
v___y_2539_ = v_trackZetaDelta_2595_;
v___y_2540_ = v_localInstances_2598_;
v___y_2541_ = v_lctx_2597_;
v___y_2542_ = v___x_2614_;
v___y_2543_ = v_cacheInferType_2604_;
goto v___jp_2532_;
}
else
{
uint8_t v_zetaDelta_2620_; 
v_zetaDelta_2620_ = lean_ctor_get_uint8(v___x_2615_, 16);
if (v_zetaDelta_2620_ == 0)
{
lean_dec_ref(v___x_2615_);
v___y_2533_ = v_zetaDeltaSet_2596_;
v___y_2534_ = v_inTypeClassResolution_2603_;
v___y_2535_ = v_canUnfold_x3f_2601_;
v___y_2536_ = v_univApprox_2602_;
v___y_2537_ = v_defEqCtx_x3f_2599_;
v___y_2538_ = v_synthPendingDepth_2600_;
v___y_2539_ = v_trackZetaDelta_2595_;
v___y_2540_ = v_localInstances_2598_;
v___y_2541_ = v_lctx_2597_;
v___y_2542_ = v___x_2614_;
v___y_2543_ = v_cacheInferType_2604_;
goto v___jp_2532_;
}
else
{
uint8_t v_etaStruct_2621_; uint8_t v_proj_2622_; uint8_t v___x_2623_; uint8_t v___x_2624_; 
v_etaStruct_2621_ = lean_ctor_get_uint8(v___x_2615_, 10);
v_proj_2622_ = lean_ctor_get_uint8(v___x_2615_, 14);
lean_dec_ref(v___x_2615_);
v___x_2623_ = 2;
v___x_2624_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
v___y_2533_ = v_zetaDeltaSet_2596_;
v___y_2534_ = v_inTypeClassResolution_2603_;
v___y_2535_ = v_canUnfold_x3f_2601_;
v___y_2536_ = v_univApprox_2602_;
v___y_2537_ = v_defEqCtx_x3f_2599_;
v___y_2538_ = v_synthPendingDepth_2600_;
v___y_2539_ = v_trackZetaDelta_2595_;
v___y_2540_ = v_localInstances_2598_;
v___y_2541_ = v_lctx_2597_;
v___y_2542_ = v___x_2614_;
v___y_2543_ = v_cacheInferType_2604_;
goto v___jp_2532_;
}
else
{
uint8_t v___x_2625_; uint8_t v___x_2626_; 
v___x_2625_ = 0;
v___x_2626_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2621_, v___x_2625_);
if (v___x_2626_ == 0)
{
v___y_2533_ = v_zetaDeltaSet_2596_;
v___y_2534_ = v_inTypeClassResolution_2603_;
v___y_2535_ = v_canUnfold_x3f_2601_;
v___y_2536_ = v_univApprox_2602_;
v___y_2537_ = v_defEqCtx_x3f_2599_;
v___y_2538_ = v_synthPendingDepth_2600_;
v___y_2539_ = v_trackZetaDelta_2595_;
v___y_2540_ = v_localInstances_2598_;
v___y_2541_ = v_lctx_2597_;
v___y_2542_ = v___x_2614_;
v___y_2543_ = v_cacheInferType_2604_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2627_; 
lean_inc(v_a_2530_);
lean_inc_ref(v_a_2529_);
lean_inc(v_a_2528_);
v___x_2627_ = lean_apply_5(v_x_2526_, v___x_2614_, v_a_2528_, v_a_2529_, v_a_2530_, lean_box(0));
return v___x_2627_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2641_, lean_object* v_x_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; uint8_t v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; uint8_t v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; uint8_t v___y_2659_; uint8_t v___y_2688_; lean_object* v___x_2746_; uint8_t v_transparency_2747_; uint8_t v___x_2748_; uint8_t v___x_2749_; 
v___x_2746_ = l_Lean_Meta_Context_config(v_a_2643_);
v_transparency_2747_ = lean_ctor_get_uint8(v___x_2746_, 9);
lean_dec_ref(v___x_2746_);
v___x_2748_ = 1;
v___x_2749_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
v___y_2688_ = v_transparency_2747_;
goto v___jp_2687_;
}
else
{
v___y_2688_ = v___x_2748_;
goto v___jp_2687_;
}
v___jp_2648_:
{
lean_object* v___x_2660_; uint8_t v_foApprox_2661_; uint8_t v_ctxApprox_2662_; uint8_t v_quasiPatternApprox_2663_; uint8_t v_constApprox_2664_; uint8_t v_isDefEqStuckEx_2665_; uint8_t v_unificationHints_2666_; uint8_t v_proofIrrelevance_2667_; uint8_t v_assignSyntheticOpaque_2668_; uint8_t v_offsetCnstrs_2669_; uint8_t v_transparency_2670_; uint8_t v_univApprox_2671_; uint8_t v_zetaUnused_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2686_; 
v___x_2660_ = l_Lean_Meta_Context_config(v___y_2658_);
lean_dec_ref(v___y_2658_);
v_foApprox_2661_ = lean_ctor_get_uint8(v___x_2660_, 0);
v_ctxApprox_2662_ = lean_ctor_get_uint8(v___x_2660_, 1);
v_quasiPatternApprox_2663_ = lean_ctor_get_uint8(v___x_2660_, 2);
v_constApprox_2664_ = lean_ctor_get_uint8(v___x_2660_, 3);
v_isDefEqStuckEx_2665_ = lean_ctor_get_uint8(v___x_2660_, 4);
v_unificationHints_2666_ = lean_ctor_get_uint8(v___x_2660_, 5);
v_proofIrrelevance_2667_ = lean_ctor_get_uint8(v___x_2660_, 6);
v_assignSyntheticOpaque_2668_ = lean_ctor_get_uint8(v___x_2660_, 7);
v_offsetCnstrs_2669_ = lean_ctor_get_uint8(v___x_2660_, 8);
v_transparency_2670_ = lean_ctor_get_uint8(v___x_2660_, 9);
v_univApprox_2671_ = lean_ctor_get_uint8(v___x_2660_, 11);
v_zetaUnused_2672_ = lean_ctor_get_uint8(v___x_2660_, 17);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2674_ = v___x_2660_;
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
else
{
lean_dec(v___x_2660_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
uint8_t v___x_2676_; uint8_t v___x_2677_; uint8_t v___x_2678_; lean_object* v___x_2680_; 
v___x_2676_ = 1;
v___x_2677_ = 0;
v___x_2678_ = 2;
if (v_isShared_2675_ == 0)
{
v___x_2680_ = v___x_2674_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 0, v_foApprox_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 1, v_ctxApprox_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 2, v_quasiPatternApprox_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 3, v_constApprox_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 4, v_isDefEqStuckEx_2665_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 5, v_unificationHints_2666_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 6, v_proofIrrelevance_2667_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 7, v_assignSyntheticOpaque_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 8, v_offsetCnstrs_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 9, v_transparency_2670_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 11, v_univApprox_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2685_, 17, v_zetaUnused_2672_);
v___x_2680_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
uint64_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_ctor_set_uint8(v___x_2680_, 10, v___x_2677_);
lean_ctor_set_uint8(v___x_2680_, 12, v___x_2676_);
lean_ctor_set_uint8(v___x_2680_, 13, v___x_2676_);
lean_ctor_set_uint8(v___x_2680_, 14, v___x_2678_);
lean_ctor_set_uint8(v___x_2680_, 15, v___x_2676_);
lean_ctor_set_uint8(v___x_2680_, 16, v___x_2676_);
lean_ctor_set_uint8(v___x_2680_, 18, v___x_2676_);
v___x_2681_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2680_);
v___x_2682_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set_uint64(v___x_2682_, sizeof(void*)*1, v___x_2681_);
lean_inc(v___y_2651_);
lean_inc(v___y_2654_);
lean_inc(v___y_2653_);
lean_inc_ref(v___y_2656_);
lean_inc_ref(v___y_2657_);
lean_inc(v___y_2649_);
v___x_2683_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___y_2649_);
lean_ctor_set(v___x_2683_, 2, v___y_2657_);
lean_ctor_set(v___x_2683_, 3, v___y_2656_);
lean_ctor_set(v___x_2683_, 4, v___y_2653_);
lean_ctor_set(v___x_2683_, 5, v___y_2654_);
lean_ctor_set(v___x_2683_, 6, v___y_2651_);
lean_ctor_set_uint8(v___x_2683_, sizeof(void*)*7, v___y_2655_);
lean_ctor_set_uint8(v___x_2683_, sizeof(void*)*7 + 1, v___y_2652_);
lean_ctor_set_uint8(v___x_2683_, sizeof(void*)*7 + 2, v___y_2650_);
lean_ctor_set_uint8(v___x_2683_, sizeof(void*)*7 + 3, v___y_2659_);
lean_inc(v_a_2646_);
lean_inc_ref(v_a_2645_);
lean_inc(v_a_2644_);
v___x_2684_ = lean_apply_5(v_x_2642_, v___x_2683_, v_a_2644_, v_a_2645_, v_a_2646_, lean_box(0));
return v___x_2684_;
}
}
}
v___jp_2687_:
{
lean_object* v___x_2689_; uint8_t v_foApprox_2690_; uint8_t v_ctxApprox_2691_; uint8_t v_quasiPatternApprox_2692_; uint8_t v_constApprox_2693_; uint8_t v_isDefEqStuckEx_2694_; uint8_t v_unificationHints_2695_; uint8_t v_proofIrrelevance_2696_; uint8_t v_assignSyntheticOpaque_2697_; uint8_t v_offsetCnstrs_2698_; uint8_t v_etaStruct_2699_; uint8_t v_univApprox_2700_; uint8_t v_iota_2701_; uint8_t v_beta_2702_; uint8_t v_proj_2703_; uint8_t v_zeta_2704_; uint8_t v_zetaDelta_2705_; uint8_t v_zetaUnused_2706_; uint8_t v_zetaHave_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2745_; 
v___x_2689_ = l_Lean_Meta_Context_config(v_a_2643_);
v_foApprox_2690_ = lean_ctor_get_uint8(v___x_2689_, 0);
v_ctxApprox_2691_ = lean_ctor_get_uint8(v___x_2689_, 1);
v_quasiPatternApprox_2692_ = lean_ctor_get_uint8(v___x_2689_, 2);
v_constApprox_2693_ = lean_ctor_get_uint8(v___x_2689_, 3);
v_isDefEqStuckEx_2694_ = lean_ctor_get_uint8(v___x_2689_, 4);
v_unificationHints_2695_ = lean_ctor_get_uint8(v___x_2689_, 5);
v_proofIrrelevance_2696_ = lean_ctor_get_uint8(v___x_2689_, 6);
v_assignSyntheticOpaque_2697_ = lean_ctor_get_uint8(v___x_2689_, 7);
v_offsetCnstrs_2698_ = lean_ctor_get_uint8(v___x_2689_, 8);
v_etaStruct_2699_ = lean_ctor_get_uint8(v___x_2689_, 10);
v_univApprox_2700_ = lean_ctor_get_uint8(v___x_2689_, 11);
v_iota_2701_ = lean_ctor_get_uint8(v___x_2689_, 12);
v_beta_2702_ = lean_ctor_get_uint8(v___x_2689_, 13);
v_proj_2703_ = lean_ctor_get_uint8(v___x_2689_, 14);
v_zeta_2704_ = lean_ctor_get_uint8(v___x_2689_, 15);
v_zetaDelta_2705_ = lean_ctor_get_uint8(v___x_2689_, 16);
v_zetaUnused_2706_ = lean_ctor_get_uint8(v___x_2689_, 17);
v_zetaHave_2707_ = lean_ctor_get_uint8(v___x_2689_, 18);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2709_ = v___x_2689_;
v_isShared_2710_ = v_isSharedCheck_2745_;
goto v_resetjp_2708_;
}
else
{
lean_dec(v___x_2689_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2745_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
uint8_t v_trackZetaDelta_2711_; lean_object* v_zetaDeltaSet_2712_; lean_object* v_lctx_2713_; lean_object* v_localInstances_2714_; lean_object* v_defEqCtx_x3f_2715_; lean_object* v_synthPendingDepth_2716_; lean_object* v_canUnfold_x3f_2717_; uint8_t v_univApprox_2718_; uint8_t v_inTypeClassResolution_2719_; uint8_t v_cacheInferType_2720_; lean_object* v_config_2722_; 
v_trackZetaDelta_2711_ = lean_ctor_get_uint8(v_a_2643_, sizeof(void*)*7);
v_zetaDeltaSet_2712_ = lean_ctor_get(v_a_2643_, 1);
v_lctx_2713_ = lean_ctor_get(v_a_2643_, 2);
v_localInstances_2714_ = lean_ctor_get(v_a_2643_, 3);
v_defEqCtx_x3f_2715_ = lean_ctor_get(v_a_2643_, 4);
v_synthPendingDepth_2716_ = lean_ctor_get(v_a_2643_, 5);
v_canUnfold_x3f_2717_ = lean_ctor_get(v_a_2643_, 6);
v_univApprox_2718_ = lean_ctor_get_uint8(v_a_2643_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2719_ = lean_ctor_get_uint8(v_a_2643_, sizeof(void*)*7 + 2);
v_cacheInferType_2720_ = lean_ctor_get_uint8(v_a_2643_, sizeof(void*)*7 + 3);
if (v_isShared_2710_ == 0)
{
v_config_2722_ = v___x_2709_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 0, v_foApprox_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 1, v_ctxApprox_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 2, v_quasiPatternApprox_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 3, v_constApprox_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 4, v_isDefEqStuckEx_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 5, v_unificationHints_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 6, v_proofIrrelevance_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 7, v_assignSyntheticOpaque_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 8, v_offsetCnstrs_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 10, v_etaStruct_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 11, v_univApprox_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 12, v_iota_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 13, v_beta_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 14, v_proj_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 15, v_zeta_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 16, v_zetaDelta_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 17, v_zetaUnused_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, 18, v_zetaHave_2707_);
v_config_2722_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
uint64_t v___x_2723_; uint64_t v___x_2724_; uint64_t v___x_2725_; uint64_t v___x_2726_; uint64_t v___x_2727_; uint64_t v_key_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v_beta_2732_; 
lean_ctor_set_uint8(v_config_2722_, 9, v___y_2688_);
v___x_2723_ = l_Lean_Meta_Context_configKey(v_a_2643_);
v___x_2724_ = 2ULL;
v___x_2725_ = lean_uint64_shift_right(v___x_2723_, v___x_2724_);
v___x_2726_ = lean_uint64_shift_left(v___x_2725_, v___x_2724_);
v___x_2727_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2688_);
v_key_2728_ = lean_uint64_lor(v___x_2726_, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2729_, 0, v_config_2722_);
lean_ctor_set_uint64(v___x_2729_, sizeof(void*)*1, v_key_2728_);
lean_inc(v_canUnfold_x3f_2717_);
lean_inc(v_synthPendingDepth_2716_);
lean_inc(v_defEqCtx_x3f_2715_);
lean_inc_ref(v_localInstances_2714_);
lean_inc_ref(v_lctx_2713_);
lean_inc(v_zetaDeltaSet_2712_);
v___x_2730_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v_zetaDeltaSet_2712_);
lean_ctor_set(v___x_2730_, 2, v_lctx_2713_);
lean_ctor_set(v___x_2730_, 3, v_localInstances_2714_);
lean_ctor_set(v___x_2730_, 4, v_defEqCtx_x3f_2715_);
lean_ctor_set(v___x_2730_, 5, v_synthPendingDepth_2716_);
lean_ctor_set(v___x_2730_, 6, v_canUnfold_x3f_2717_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*7, v_trackZetaDelta_2711_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*7 + 1, v_univApprox_2718_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2719_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*7 + 3, v_cacheInferType_2720_);
v___x_2731_ = l_Lean_Meta_Context_config(v___x_2730_);
v_beta_2732_ = lean_ctor_get_uint8(v___x_2731_, 13);
if (v_beta_2732_ == 0)
{
lean_dec_ref(v___x_2731_);
v___y_2649_ = v_zetaDeltaSet_2712_;
v___y_2650_ = v_inTypeClassResolution_2719_;
v___y_2651_ = v_canUnfold_x3f_2717_;
v___y_2652_ = v_univApprox_2718_;
v___y_2653_ = v_defEqCtx_x3f_2715_;
v___y_2654_ = v_synthPendingDepth_2716_;
v___y_2655_ = v_trackZetaDelta_2711_;
v___y_2656_ = v_localInstances_2714_;
v___y_2657_ = v_lctx_2713_;
v___y_2658_ = v___x_2730_;
v___y_2659_ = v_cacheInferType_2720_;
goto v___jp_2648_;
}
else
{
uint8_t v_iota_2733_; 
v_iota_2733_ = lean_ctor_get_uint8(v___x_2731_, 12);
if (v_iota_2733_ == 0)
{
lean_dec_ref(v___x_2731_);
v___y_2649_ = v_zetaDeltaSet_2712_;
v___y_2650_ = v_inTypeClassResolution_2719_;
v___y_2651_ = v_canUnfold_x3f_2717_;
v___y_2652_ = v_univApprox_2718_;
v___y_2653_ = v_defEqCtx_x3f_2715_;
v___y_2654_ = v_synthPendingDepth_2716_;
v___y_2655_ = v_trackZetaDelta_2711_;
v___y_2656_ = v_localInstances_2714_;
v___y_2657_ = v_lctx_2713_;
v___y_2658_ = v___x_2730_;
v___y_2659_ = v_cacheInferType_2720_;
goto v___jp_2648_;
}
else
{
uint8_t v_zeta_2734_; 
v_zeta_2734_ = lean_ctor_get_uint8(v___x_2731_, 15);
if (v_zeta_2734_ == 0)
{
lean_dec_ref(v___x_2731_);
v___y_2649_ = v_zetaDeltaSet_2712_;
v___y_2650_ = v_inTypeClassResolution_2719_;
v___y_2651_ = v_canUnfold_x3f_2717_;
v___y_2652_ = v_univApprox_2718_;
v___y_2653_ = v_defEqCtx_x3f_2715_;
v___y_2654_ = v_synthPendingDepth_2716_;
v___y_2655_ = v_trackZetaDelta_2711_;
v___y_2656_ = v_localInstances_2714_;
v___y_2657_ = v_lctx_2713_;
v___y_2658_ = v___x_2730_;
v___y_2659_ = v_cacheInferType_2720_;
goto v___jp_2648_;
}
else
{
uint8_t v_zetaHave_2735_; 
v_zetaHave_2735_ = lean_ctor_get_uint8(v___x_2731_, 18);
if (v_zetaHave_2735_ == 0)
{
lean_dec_ref(v___x_2731_);
v___y_2649_ = v_zetaDeltaSet_2712_;
v___y_2650_ = v_inTypeClassResolution_2719_;
v___y_2651_ = v_canUnfold_x3f_2717_;
v___y_2652_ = v_univApprox_2718_;
v___y_2653_ = v_defEqCtx_x3f_2715_;
v___y_2654_ = v_synthPendingDepth_2716_;
v___y_2655_ = v_trackZetaDelta_2711_;
v___y_2656_ = v_localInstances_2714_;
v___y_2657_ = v_lctx_2713_;
v___y_2658_ = v___x_2730_;
v___y_2659_ = v_cacheInferType_2720_;
goto v___jp_2648_;
}
else
{
uint8_t v_zetaDelta_2736_; 
v_zetaDelta_2736_ = lean_ctor_get_uint8(v___x_2731_, 16);
if (v_zetaDelta_2736_ == 0)
{
lean_dec_ref(v___x_2731_);
v___y_2649_ = v_zetaDeltaSet_2712_;
v___y_2650_ = v_inTypeClassResolution_2719_;
v___y_2651_ = v_canUnfold_x3f_2717_;
v___y_2652_ = v_univApprox_2718_;
v___y_2653_ = v_defEqCtx_x3f_2715_;
v___y_2654_ = v_synthPendingDepth_2716_;
v___y_2655_ = v_trackZetaDelta_2711_;
v___y_2656_ = v_localInstances_2714_;
v___y_2657_ = v_lctx_2713_;
v___y_2658_ = v___x_2730_;
v___y_2659_ = v_cacheInferType_2720_;
goto v___jp_2648_;
}
else
{
uint8_t v_etaStruct_2737_; uint8_t v_proj_2738_; uint8_t v___x_2739_; uint8_t v___x_2740_; 
v_etaStruct_2737_ = lean_ctor_get_uint8(v___x_2731_, 10);
v_proj_2738_ = lean_ctor_get_uint8(v___x_2731_, 14);
lean_dec_ref(v___x_2731_);
v___x_2739_ = 2;
v___x_2740_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
v___y_2649_ = v_zetaDeltaSet_2712_;
v___y_2650_ = v_inTypeClassResolution_2719_;
v___y_2651_ = v_canUnfold_x3f_2717_;
v___y_2652_ = v_univApprox_2718_;
v___y_2653_ = v_defEqCtx_x3f_2715_;
v___y_2654_ = v_synthPendingDepth_2716_;
v___y_2655_ = v_trackZetaDelta_2711_;
v___y_2656_ = v_localInstances_2714_;
v___y_2657_ = v_lctx_2713_;
v___y_2658_ = v___x_2730_;
v___y_2659_ = v_cacheInferType_2720_;
goto v___jp_2648_;
}
else
{
uint8_t v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = 0;
v___x_2742_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2737_, v___x_2741_);
if (v___x_2742_ == 0)
{
v___y_2649_ = v_zetaDeltaSet_2712_;
v___y_2650_ = v_inTypeClassResolution_2719_;
v___y_2651_ = v_canUnfold_x3f_2717_;
v___y_2652_ = v_univApprox_2718_;
v___y_2653_ = v_defEqCtx_x3f_2715_;
v___y_2654_ = v_synthPendingDepth_2716_;
v___y_2655_ = v_trackZetaDelta_2711_;
v___y_2656_ = v_localInstances_2714_;
v___y_2657_ = v_lctx_2713_;
v___y_2658_ = v___x_2730_;
v___y_2659_ = v_cacheInferType_2720_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2743_; 
lean_inc(v_a_2646_);
lean_inc_ref(v_a_2645_);
lean_inc(v_a_2644_);
v___x_2743_ = lean_apply_5(v_x_2642_, v___x_2730_, v_a_2644_, v_a_2645_, v_a_2646_, lean_box(0));
return v___x_2743_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2750_, lean_object* v_x_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2750_, v_x_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2757_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2758_ = lean_box(0);
v___x_2759_ = l_Lean_interruptExceptionId;
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___x_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___closed__0);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b1_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b1_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b1_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_, lean_object* v_x_2779_){
_start:
{
lean_object* v_ks_2780_; lean_object* v_vs_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2810_; 
v_ks_2780_ = lean_ctor_get(v_x_2776_, 0);
v_vs_2781_ = lean_ctor_get(v_x_2776_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_x_2776_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2783_ = v_x_2776_;
v_isShared_2784_ = v_isSharedCheck_2810_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_vs_2781_);
lean_inc(v_ks_2780_);
lean_dec(v_x_2776_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2810_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
uint8_t v___y_2786_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2798_ = lean_array_get_size(v_ks_2780_);
v___x_2799_ = lean_nat_dec_lt(v_x_2777_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2783_);
lean_dec(v_x_2777_);
v___x_2800_ = lean_array_push(v_ks_2780_, v_x_2778_);
v___x_2801_ = lean_array_push(v_vs_2781_, v_x_2779_);
v___x_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
return v___x_2802_;
}
else
{
lean_object* v_expr_2803_; uint64_t v_configKey_2804_; lean_object* v_k_x27_2805_; lean_object* v_expr_2806_; uint64_t v_configKey_2807_; uint8_t v___x_2808_; 
v_expr_2803_ = lean_ctor_get(v_x_2778_, 0);
v_configKey_2804_ = lean_ctor_get_uint64(v_x_2778_, sizeof(void*)*1);
v_k_x27_2805_ = lean_array_fget_borrowed(v_ks_2780_, v_x_2777_);
v_expr_2806_ = lean_ctor_get(v_k_x27_2805_, 0);
v_configKey_2807_ = lean_ctor_get_uint64(v_k_x27_2805_, sizeof(void*)*1);
v___x_2808_ = lean_expr_equal(v_expr_2803_, v_expr_2806_);
if (v___x_2808_ == 0)
{
v___y_2786_ = v___x_2808_;
goto v___jp_2785_;
}
else
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_uint64_dec_eq(v_configKey_2804_, v_configKey_2807_);
v___y_2786_ = v___x_2809_;
goto v___jp_2785_;
}
}
v___jp_2785_:
{
if (v___y_2786_ == 0)
{
lean_object* v___x_2788_; 
if (v_isShared_2784_ == 0)
{
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_ks_2780_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_vs_2781_);
v___x_2788_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_nat_add(v_x_2777_, v___x_2789_);
lean_dec(v_x_2777_);
v_x_2776_ = v___x_2788_;
v_x_2777_ = v___x_2790_;
goto _start;
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_array_fset(v_ks_2780_, v_x_2777_, v_x_2778_);
v___x_2794_ = lean_array_fset(v_vs_2781_, v_x_2777_, v_x_2779_);
lean_dec(v_x_2777_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2794_);
lean_ctor_set(v___x_2783_, 0, v___x_2793_);
v___x_2796_ = v___x_2783_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(lean_object* v_n_2811_, lean_object* v_k_2812_, lean_object* v_v_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_unsigned_to_nat(0u);
v___x_2815_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2811_, v___x_2814_, v_k_2812_, v_v_2813_);
return v___x_2815_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(lean_object* v_x_2817_, size_t v_x_2818_, size_t v_x_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 0)
{
lean_object* v_es_2822_; size_t v___x_2823_; size_t v___x_2824_; size_t v___x_2825_; size_t v___x_2826_; lean_object* v_j_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v_es_2822_ = lean_ctor_get(v_x_2817_, 0);
v___x_2823_ = ((size_t)5ULL);
v___x_2824_ = ((size_t)1ULL);
v___x_2825_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2826_ = lean_usize_land(v_x_2818_, v___x_2825_);
v_j_2827_ = lean_usize_to_nat(v___x_2826_);
v___x_2828_ = lean_array_get_size(v_es_2822_);
v___x_2829_ = lean_nat_dec_lt(v_j_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_dec(v_j_2827_);
lean_dec(v_x_2821_);
lean_dec_ref(v_x_2820_);
return v_x_2817_;
}
else
{
lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2873_; 
lean_inc_ref(v_es_2822_);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v_x_2817_, 0);
lean_dec(v_unused_2874_);
v___x_2831_ = v_x_2817_;
v_isShared_2832_ = v_isSharedCheck_2873_;
goto v_resetjp_2830_;
}
else
{
lean_dec(v_x_2817_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2873_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_v_2833_; lean_object* v___x_2834_; lean_object* v_xs_x27_2835_; lean_object* v___y_2837_; 
v_v_2833_ = lean_array_fget(v_es_2822_, v_j_2827_);
v___x_2834_ = lean_box(0);
v_xs_x27_2835_ = lean_array_fset(v_es_2822_, v_j_2827_, v___x_2834_);
switch(lean_obj_tag(v_v_2833_))
{
case 0:
{
lean_object* v_key_2842_; lean_object* v_val_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2860_; 
v_key_2842_ = lean_ctor_get(v_v_2833_, 0);
v_val_2843_ = lean_ctor_get(v_v_2833_, 1);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_v_2833_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2845_ = v_v_2833_;
v_isShared_2846_ = v_isSharedCheck_2860_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_val_2843_);
lean_inc(v_key_2842_);
lean_dec(v_v_2833_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2860_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
uint8_t v___y_2848_; lean_object* v_expr_2854_; uint64_t v_configKey_2855_; lean_object* v_expr_2856_; uint64_t v_configKey_2857_; uint8_t v___x_2858_; 
v_expr_2854_ = lean_ctor_get(v_x_2820_, 0);
v_configKey_2855_ = lean_ctor_get_uint64(v_x_2820_, sizeof(void*)*1);
v_expr_2856_ = lean_ctor_get(v_key_2842_, 0);
v_configKey_2857_ = lean_ctor_get_uint64(v_key_2842_, sizeof(void*)*1);
v___x_2858_ = lean_expr_equal(v_expr_2854_, v_expr_2856_);
if (v___x_2858_ == 0)
{
v___y_2848_ = v___x_2858_;
goto v___jp_2847_;
}
else
{
uint8_t v___x_2859_; 
v___x_2859_ = lean_uint64_dec_eq(v_configKey_2855_, v_configKey_2857_);
v___y_2848_ = v___x_2859_;
goto v___jp_2847_;
}
v___jp_2847_:
{
if (v___y_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_del_object(v___x_2845_);
v___x_2849_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2842_, v_val_2843_, v_x_2820_, v_x_2821_);
v___x_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
v___y_2837_ = v___x_2850_;
goto v___jp_2836_;
}
else
{
lean_object* v___x_2852_; 
lean_dec(v_val_2843_);
lean_dec(v_key_2842_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v_x_2821_);
lean_ctor_set(v___x_2845_, 0, v_x_2820_);
v___x_2852_ = v___x_2845_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_x_2820_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_x_2821_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
v___y_2837_ = v___x_2852_;
goto v___jp_2836_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2871_; 
v_node_2861_ = lean_ctor_get(v_v_2833_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_v_2833_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2863_ = v_v_2833_;
v_isShared_2864_ = v_isSharedCheck_2871_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_node_2861_);
lean_dec(v_v_2833_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2871_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
size_t v___x_2865_; size_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2865_ = lean_usize_shift_right(v_x_2818_, v___x_2823_);
v___x_2866_ = lean_usize_add(v_x_2819_, v___x_2824_);
v___x_2867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_node_2861_, v___x_2865_, v___x_2866_, v_x_2820_, v_x_2821_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2867_);
v___x_2869_ = v___x_2863_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
v___y_2837_ = v___x_2869_;
goto v___jp_2836_;
}
}
}
default: 
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v_x_2820_);
lean_ctor_set(v___x_2872_, 1, v_x_2821_);
v___y_2837_ = v___x_2872_;
goto v___jp_2836_;
}
}
v___jp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2838_ = lean_array_fset(v_xs_x27_2835_, v_j_2827_, v___y_2837_);
lean_dec(v_j_2827_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2838_);
v___x_2840_ = v___x_2831_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
else
{
lean_object* v_ks_2875_; lean_object* v_vs_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2896_; 
v_ks_2875_ = lean_ctor_get(v_x_2817_, 0);
v_vs_2876_ = lean_ctor_get(v_x_2817_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2878_ = v_x_2817_;
v_isShared_2879_ = v_isSharedCheck_2896_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_vs_2876_);
lean_inc(v_ks_2875_);
lean_dec(v_x_2817_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2896_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_ks_2875_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_vs_2876_);
v___x_2881_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v_newNode_2882_; uint8_t v___y_2884_; size_t v___x_2890_; uint8_t v___x_2891_; 
v_newNode_2882_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v___x_2881_, v_x_2820_, v_x_2821_);
v___x_2890_ = ((size_t)7ULL);
v___x_2891_ = lean_usize_dec_le(v___x_2890_, v_x_2819_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v___x_2892_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2882_);
v___x_2893_ = lean_unsigned_to_nat(4u);
v___x_2894_ = lean_nat_dec_lt(v___x_2892_, v___x_2893_);
lean_dec(v___x_2892_);
v___y_2884_ = v___x_2894_;
goto v___jp_2883_;
}
else
{
v___y_2884_ = v___x_2891_;
goto v___jp_2883_;
}
v___jp_2883_:
{
if (v___y_2884_ == 0)
{
lean_object* v_ks_2885_; lean_object* v_vs_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_ks_2885_ = lean_ctor_get(v_newNode_2882_, 0);
lean_inc_ref(v_ks_2885_);
v_vs_2886_ = lean_ctor_get(v_newNode_2882_, 1);
lean_inc_ref(v_vs_2886_);
lean_dec_ref(v_newNode_2882_);
v___x_2887_ = lean_unsigned_to_nat(0u);
v___x_2888_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___closed__0);
v___x_2889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_x_2819_, v_ks_2885_, v_vs_2886_, v___x_2887_, v___x_2888_);
lean_dec_ref(v_vs_2886_);
lean_dec_ref(v_ks_2885_);
return v___x_2889_;
}
else
{
return v_newNode_2882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(size_t v_depth_2897_, lean_object* v_keys_2898_, lean_object* v_vals_2899_, lean_object* v_i_2900_, lean_object* v_entries_2901_){
_start:
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = lean_array_get_size(v_keys_2898_);
v___x_2903_ = lean_nat_dec_lt(v_i_2900_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_dec(v_i_2900_);
return v_entries_2901_;
}
else
{
lean_object* v_k_2904_; lean_object* v_expr_2905_; uint64_t v_configKey_2906_; lean_object* v_v_2907_; uint64_t v___x_2908_; uint64_t v___x_2909_; size_t v_h_2910_; size_t v___x_2911_; lean_object* v___x_2912_; size_t v___x_2913_; size_t v___x_2914_; size_t v___x_2915_; size_t v_h_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_k_2904_ = lean_array_fget_borrowed(v_keys_2898_, v_i_2900_);
v_expr_2905_ = lean_ctor_get(v_k_2904_, 0);
v_configKey_2906_ = lean_ctor_get_uint64(v_k_2904_, sizeof(void*)*1);
v_v_2907_ = lean_array_fget_borrowed(v_vals_2899_, v_i_2900_);
v___x_2908_ = l_Lean_Expr_hash(v_expr_2905_);
v___x_2909_ = lean_uint64_mix_hash(v___x_2908_, v_configKey_2906_);
v_h_2910_ = lean_uint64_to_usize(v___x_2909_);
v___x_2911_ = ((size_t)5ULL);
v___x_2912_ = lean_unsigned_to_nat(1u);
v___x_2913_ = ((size_t)1ULL);
v___x_2914_ = lean_usize_sub(v_depth_2897_, v___x_2913_);
v___x_2915_ = lean_usize_mul(v___x_2911_, v___x_2914_);
v_h_2916_ = lean_usize_shift_right(v_h_2910_, v___x_2915_);
v___x_2917_ = lean_nat_add(v_i_2900_, v___x_2912_);
lean_dec(v_i_2900_);
lean_inc(v_v_2907_);
lean_inc(v_k_2904_);
v___x_2918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_entries_2901_, v_h_2916_, v_depth_2897_, v_k_2904_, v_v_2907_);
v_i_2900_ = v___x_2917_;
v_entries_2901_ = v___x_2918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_2920_, lean_object* v_keys_2921_, lean_object* v_vals_2922_, lean_object* v_i_2923_, lean_object* v_entries_2924_){
_start:
{
size_t v_depth_boxed_2925_; lean_object* v_res_2926_; 
v_depth_boxed_2925_ = lean_unbox_usize(v_depth_2920_);
lean_dec(v_depth_2920_);
v_res_2926_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_boxed_2925_, v_keys_2921_, v_vals_2922_, v_i_2923_, v_entries_2924_);
lean_dec_ref(v_vals_2922_);
lean_dec_ref(v_keys_2921_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg___boxed(lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
size_t v_x_2774__boxed_2932_; size_t v_x_2775__boxed_2933_; lean_object* v_res_2934_; 
v_x_2774__boxed_2932_ = lean_unbox_usize(v_x_2928_);
lean_dec(v_x_2928_);
v_x_2775__boxed_2933_ = lean_unbox_usize(v_x_2929_);
lean_dec(v_x_2929_);
v_res_2934_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2927_, v_x_2774__boxed_2932_, v_x_2775__boxed_2933_, v_x_2930_, v_x_2931_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_){
_start:
{
lean_object* v_expr_2938_; uint64_t v_configKey_2939_; uint64_t v___x_2940_; uint64_t v___x_2941_; size_t v___x_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v_expr_2938_ = lean_ctor_get(v_x_2936_, 0);
v_configKey_2939_ = lean_ctor_get_uint64(v_x_2936_, sizeof(void*)*1);
v___x_2940_ = l_Lean_Expr_hash(v_expr_2938_);
v___x_2941_ = lean_uint64_mix_hash(v___x_2940_, v_configKey_2939_);
v___x_2942_ = lean_uint64_to_usize(v___x_2941_);
v___x_2943_ = ((size_t)1ULL);
v___x_2944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_2935_, v___x_2942_, v___x_2943_, v_x_2936_, v_x_2937_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_2945_, lean_object* v_vals_2946_, lean_object* v_i_2947_, lean_object* v_k_2948_){
_start:
{
uint8_t v___y_2950_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = lean_array_get_size(v_keys_2945_);
v___x_2957_ = lean_nat_dec_lt(v_i_2947_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; 
lean_dec(v_i_2947_);
v___x_2958_ = lean_box(0);
return v___x_2958_;
}
else
{
lean_object* v_expr_2959_; uint64_t v_configKey_2960_; lean_object* v_k_x27_2961_; lean_object* v_expr_2962_; uint64_t v_configKey_2963_; uint8_t v___x_2964_; 
v_expr_2959_ = lean_ctor_get(v_k_2948_, 0);
v_configKey_2960_ = lean_ctor_get_uint64(v_k_2948_, sizeof(void*)*1);
v_k_x27_2961_ = lean_array_fget_borrowed(v_keys_2945_, v_i_2947_);
v_expr_2962_ = lean_ctor_get(v_k_x27_2961_, 0);
v_configKey_2963_ = lean_ctor_get_uint64(v_k_x27_2961_, sizeof(void*)*1);
v___x_2964_ = lean_expr_equal(v_expr_2959_, v_expr_2962_);
if (v___x_2964_ == 0)
{
v___y_2950_ = v___x_2964_;
goto v___jp_2949_;
}
else
{
uint8_t v___x_2965_; 
v___x_2965_ = lean_uint64_dec_eq(v_configKey_2960_, v_configKey_2963_);
v___y_2950_ = v___x_2965_;
goto v___jp_2949_;
}
}
v___jp_2949_:
{
if (v___y_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_nat_add(v_i_2947_, v___x_2951_);
lean_dec(v_i_2947_);
v_i_2947_ = v___x_2952_;
goto _start;
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_array_fget_borrowed(v_vals_2946_, v_i_2947_);
lean_dec(v_i_2947_);
lean_inc(v___x_2954_);
v___x_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
return v___x_2955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_2966_, lean_object* v_vals_2967_, lean_object* v_i_2968_, lean_object* v_k_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_2966_, v_vals_2967_, v_i_2968_, v_k_2969_);
lean_dec_ref(v_k_2969_);
lean_dec_ref(v_vals_2967_);
lean_dec_ref(v_keys_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(lean_object* v_x_2971_, size_t v_x_2972_, lean_object* v_x_2973_){
_start:
{
if (lean_obj_tag(v_x_2971_) == 0)
{
lean_object* v_es_2974_; lean_object* v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; size_t v___x_2978_; lean_object* v_j_2979_; lean_object* v___x_2980_; 
v_es_2974_ = lean_ctor_get(v_x_2971_, 0);
v___x_2975_ = lean_box(2);
v___x_2976_ = ((size_t)5ULL);
v___x_2977_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2978_ = lean_usize_land(v_x_2972_, v___x_2977_);
v_j_2979_ = lean_usize_to_nat(v___x_2978_);
v___x_2980_ = lean_array_get_borrowed(v___x_2975_, v_es_2974_, v_j_2979_);
lean_dec(v_j_2979_);
switch(lean_obj_tag(v___x_2980_))
{
case 0:
{
lean_object* v_key_2981_; lean_object* v_val_2982_; uint8_t v___y_2984_; lean_object* v_expr_2987_; uint64_t v_configKey_2988_; lean_object* v_expr_2989_; uint64_t v_configKey_2990_; uint8_t v___x_2991_; 
v_key_2981_ = lean_ctor_get(v___x_2980_, 0);
v_val_2982_ = lean_ctor_get(v___x_2980_, 1);
v_expr_2987_ = lean_ctor_get(v_x_2973_, 0);
v_configKey_2988_ = lean_ctor_get_uint64(v_x_2973_, sizeof(void*)*1);
v_expr_2989_ = lean_ctor_get(v_key_2981_, 0);
v_configKey_2990_ = lean_ctor_get_uint64(v_key_2981_, sizeof(void*)*1);
v___x_2991_ = lean_expr_equal(v_expr_2987_, v_expr_2989_);
if (v___x_2991_ == 0)
{
v___y_2984_ = v___x_2991_;
goto v___jp_2983_;
}
else
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_uint64_dec_eq(v_configKey_2988_, v_configKey_2990_);
v___y_2984_ = v___x_2992_;
goto v___jp_2983_;
}
v___jp_2983_:
{
if (v___y_2984_ == 0)
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_box(0);
return v___x_2985_;
}
else
{
lean_object* v___x_2986_; 
lean_inc(v_val_2982_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_val_2982_);
return v___x_2986_;
}
}
}
case 1:
{
lean_object* v_node_2993_; size_t v___x_2994_; 
v_node_2993_ = lean_ctor_get(v___x_2980_, 0);
v___x_2994_ = lean_usize_shift_right(v_x_2972_, v___x_2976_);
v_x_2971_ = v_node_2993_;
v_x_2972_ = v___x_2994_;
goto _start;
}
default: 
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_box(0);
return v___x_2996_;
}
}
}
else
{
lean_object* v_ks_2997_; lean_object* v_vs_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_ks_2997_ = lean_ctor_get(v_x_2971_, 0);
v_vs_2998_ = lean_ctor_get(v_x_2971_, 1);
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_ks_2997_, v_vs_2998_, v___x_2999_, v_x_2973_);
return v___x_3000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg___boxed(lean_object* v_x_3001_, lean_object* v_x_3002_, lean_object* v_x_3003_){
_start:
{
size_t v_x_2989__boxed_3004_; lean_object* v_res_3005_; 
v_x_2989__boxed_3004_ = lean_unbox_usize(v_x_3002_);
lean_dec(v_x_3002_);
v_res_3005_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3001_, v_x_2989__boxed_3004_, v_x_3003_);
lean_dec_ref(v_x_3003_);
lean_dec_ref(v_x_3001_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(lean_object* v_x_3006_, lean_object* v_x_3007_){
_start:
{
lean_object* v_expr_3008_; uint64_t v_configKey_3009_; uint64_t v___x_3010_; uint64_t v___x_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v_expr_3008_ = lean_ctor_get(v_x_3007_, 0);
v_configKey_3009_ = lean_ctor_get_uint64(v_x_3007_, sizeof(void*)*1);
v___x_3010_ = l_Lean_Expr_hash(v_expr_3008_);
v___x_3011_ = lean_uint64_mix_hash(v___x_3010_, v_configKey_3009_);
v___x_3012_ = lean_uint64_to_usize(v___x_3011_);
v___x_3013_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3006_, v___x_3012_, v_x_3007_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg___boxed(lean_object* v_x_3014_, lean_object* v_x_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3014_, v_x_3015_);
lean_dec_ref(v_x_3015_);
lean_dec_ref(v_x_3014_);
return v_res_3016_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_3019_ = l_Lean_stringToMessageData(v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
switch(lean_obj_tag(v_e_3020_))
{
case 0:
{
lean_object* v_deBruijnIndex_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_deBruijnIndex_3056_ = lean_ctor_get(v_e_3020_, 0);
lean_inc(v_deBruijnIndex_3056_);
lean_dec_ref(v_e_3020_);
v___x_3057_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_3058_ = l_Lean_mkBVar(v_deBruijnIndex_3056_);
v___x_3059_ = l_Lean_MessageData_ofExpr(v___x_3058_);
v___x_3060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3057_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_3060_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3061_;
}
case 1:
{
lean_object* v_fvarId_3062_; lean_object* v___x_3063_; 
v_fvarId_3062_ = lean_ctor_get(v_e_3020_, 0);
lean_inc(v_fvarId_3062_);
lean_dec_ref(v_e_3020_);
v___x_3063_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3062_, v_a_3021_, v_a_3023_, v_a_3024_);
return v___x_3063_;
}
case 2:
{
lean_object* v_mvarId_3064_; lean_object* v___x_3065_; 
v_mvarId_3064_ = lean_ctor_get(v_e_3020_, 0);
lean_inc(v_mvarId_3064_);
lean_dec_ref(v_e_3020_);
v___x_3065_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3064_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3065_;
}
case 3:
{
lean_object* v_u_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_u_3066_ = lean_ctor_get(v_e_3020_, 0);
lean_inc(v_u_3066_);
lean_dec_ref(v_e_3020_);
v___x_3067_ = l_Lean_Level_succ___override(v_u_3066_);
v___x_3068_ = l_Lean_mkSort(v___x_3067_);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
case 4:
{
lean_object* v_declName_3070_; lean_object* v_us_3071_; 
v_declName_3070_ = lean_ctor_get(v_e_3020_, 0);
lean_inc(v_declName_3070_);
v_us_3071_ = lean_ctor_get(v_e_3020_, 1);
lean_inc(v_us_3071_);
if (lean_obj_tag(v_us_3071_) == 0)
{
lean_object* v___x_3087_; 
lean_dec_ref(v_e_3020_);
v___x_3087_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3070_, v_us_3071_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3087_;
}
else
{
uint8_t v_cacheInferType_3088_; 
v_cacheInferType_3088_ = lean_ctor_get_uint8(v_a_3021_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3088_ == 0)
{
lean_dec_ref(v_e_3020_);
goto v___jp_3072_;
}
else
{
uint8_t v___x_3089_; 
v___x_3089_ = l_Lean_Expr_hasMVar(v_e_3020_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3155_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3155_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3155_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3135_; lean_object* v_cache_3136_; lean_object* v_inferType_3137_; lean_object* v___x_3138_; 
v___x_3135_ = lean_st_ref_get(v_a_3022_);
v_cache_3136_ = lean_ctor_get(v___x_3135_, 1);
lean_inc_ref(v_cache_3136_);
lean_dec(v___x_3135_);
v_inferType_3137_ = lean_ctor_get(v_cache_3136_, 0);
lean_inc_ref(v_inferType_3137_);
lean_dec_ref(v_cache_3136_);
v___x_3138_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3137_, v_a_3091_);
lean_dec_ref(v_inferType_3137_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_cancelTk_x3f_3139_; 
lean_del_object(v___x_3093_);
v_cancelTk_x3f_3139_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3139_) == 1)
{
lean_object* v_val_3140_; uint8_t v___x_3141_; 
v_val_3140_ = lean_ctor_get(v_cancelTk_x3f_3139_, 0);
v___x_3141_ = l_IO_CancelToken_isSet(v_val_3140_);
if (v___x_3141_ == 0)
{
goto v___jp_3095_;
}
else
{
lean_object* v___x_3142_; lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v_a_3091_);
lean_dec(v_us_3071_);
lean_dec(v_declName_3070_);
v___x_3142_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
goto v___jp_3095_;
}
}
else
{
lean_object* v_val_3151_; lean_object* v___x_3153_; 
lean_dec(v_a_3091_);
lean_dec(v_us_3071_);
lean_dec(v_declName_3070_);
v_val_3151_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_val_3151_);
lean_dec_ref(v___x_3138_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v_val_3151_);
v___x_3153_ = v___x_3093_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_val_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
v___jp_3095_:
{
lean_object* v___x_3096_; 
v___x_3096_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3070_, v_us_3071_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; uint8_t v___x_3098_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
v___x_3098_ = l_Lean_Expr_hasMVar(v_a_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3133_; 
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___x_3096_, 0);
lean_dec(v_unused_3134_);
v___x_3100_ = v___x_3096_;
v_isShared_3101_ = v_isSharedCheck_3133_;
goto v_resetjp_3099_;
}
else
{
lean_dec(v___x_3096_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3133_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v_cache_3103_; lean_object* v_mctx_3104_; lean_object* v_zetaDeltaFVarIds_3105_; lean_object* v_postponed_3106_; lean_object* v_diag_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3132_; 
v___x_3102_ = lean_st_ref_take(v_a_3022_);
v_cache_3103_ = lean_ctor_get(v___x_3102_, 1);
v_mctx_3104_ = lean_ctor_get(v___x_3102_, 0);
v_zetaDeltaFVarIds_3105_ = lean_ctor_get(v___x_3102_, 2);
v_postponed_3106_ = lean_ctor_get(v___x_3102_, 3);
v_diag_3107_ = lean_ctor_get(v___x_3102_, 4);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3109_ = v___x_3102_;
v_isShared_3110_ = v_isSharedCheck_3132_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_diag_3107_);
lean_inc(v_postponed_3106_);
lean_inc(v_zetaDeltaFVarIds_3105_);
lean_inc(v_cache_3103_);
lean_inc(v_mctx_3104_);
lean_dec(v___x_3102_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3132_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v_inferType_3111_; lean_object* v_funInfo_3112_; lean_object* v_synthInstance_3113_; lean_object* v_whnf_3114_; lean_object* v_defEqTrans_3115_; lean_object* v_defEqPerm_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3131_; 
v_inferType_3111_ = lean_ctor_get(v_cache_3103_, 0);
v_funInfo_3112_ = lean_ctor_get(v_cache_3103_, 1);
v_synthInstance_3113_ = lean_ctor_get(v_cache_3103_, 2);
v_whnf_3114_ = lean_ctor_get(v_cache_3103_, 3);
v_defEqTrans_3115_ = lean_ctor_get(v_cache_3103_, 4);
v_defEqPerm_3116_ = lean_ctor_get(v_cache_3103_, 5);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_cache_3103_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3118_ = v_cache_3103_;
v_isShared_3119_ = v_isSharedCheck_3131_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_defEqPerm_3116_);
lean_inc(v_defEqTrans_3115_);
lean_inc(v_whnf_3114_);
lean_inc(v_synthInstance_3113_);
lean_inc(v_funInfo_3112_);
lean_inc(v_inferType_3111_);
lean_dec(v_cache_3103_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3131_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_inc(v_a_3097_);
v___x_3120_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3111_, v_a_3091_, v_a_3097_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3120_);
v___x_3122_ = v___x_3118_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_funInfo_3112_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_synthInstance_3113_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v_whnf_3114_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_defEqTrans_3115_);
lean_ctor_set(v_reuseFailAlloc_3130_, 5, v_defEqPerm_3116_);
v___x_3122_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 1, v___x_3122_);
v___x_3124_ = v___x_3109_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_mctx_3104_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_zetaDeltaFVarIds_3105_);
lean_ctor_set(v_reuseFailAlloc_3129_, 3, v_postponed_3106_);
lean_ctor_set(v_reuseFailAlloc_3129_, 4, v_diag_3107_);
v___x_3124_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = lean_st_ref_set(v_a_3022_, v___x_3124_);
if (v_isShared_3101_ == 0)
{
v___x_3127_ = v___x_3100_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3097_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3097_);
lean_dec(v_a_3091_);
return v___x_3096_;
}
}
else
{
lean_dec(v_a_3091_);
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_us_3071_);
lean_dec(v_declName_3070_);
v_a_3156_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3090_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3090_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_dec_ref(v_e_3020_);
goto v___jp_3072_;
}
}
}
v___jp_3072_:
{
lean_object* v_cancelTk_x3f_3073_; 
v_cancelTk_x3f_3073_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3073_) == 1)
{
lean_object* v_val_3074_; uint8_t v___x_3075_; 
v_val_3074_ = lean_ctor_get(v_cancelTk_x3f_3073_, 0);
v___x_3075_ = l_IO_CancelToken_isSet(v_val_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3070_, v_us_3071_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_us_3071_);
lean_dec(v_declName_3070_);
v___x_3077_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3070_, v_us_3071_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3086_;
}
}
}
case 5:
{
lean_object* v_fn_3164_; uint8_t v_cacheInferType_3165_; lean_object* v_nargs_3166_; lean_object* v___x_3167_; lean_object* v_dummy_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_fn_3164_ = lean_ctor_get(v_e_3020_, 0);
v_cacheInferType_3165_ = lean_ctor_get_uint8(v_a_3021_, sizeof(void*)*7 + 3);
v_nargs_3166_ = l_Lean_Expr_getAppNumArgs(v_e_3020_);
v___x_3167_ = l_Lean_Expr_getAppFn(v_fn_3164_);
v_dummy_3168_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3166_);
v___x_3169_ = lean_mk_array(v_nargs_3166_, v_dummy_3168_);
v___x_3170_ = lean_unsigned_to_nat(1u);
v___x_3171_ = lean_nat_sub(v_nargs_3166_, v___x_3170_);
lean_dec(v_nargs_3166_);
lean_inc_ref(v_e_3020_);
v___x_3172_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3020_, v___x_3169_, v___x_3171_);
if (v_cacheInferType_3165_ == 0)
{
lean_dec_ref(v_e_3020_);
goto v___jp_3173_;
}
else
{
uint8_t v___x_3188_; 
v___x_3188_ = l_Lean_Expr_hasMVar(v_e_3020_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3254_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3254_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3254_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3234_; lean_object* v_cache_3235_; lean_object* v_inferType_3236_; lean_object* v___x_3237_; 
v___x_3234_ = lean_st_ref_get(v_a_3022_);
v_cache_3235_ = lean_ctor_get(v___x_3234_, 1);
lean_inc_ref(v_cache_3235_);
lean_dec(v___x_3234_);
v_inferType_3236_ = lean_ctor_get(v_cache_3235_, 0);
lean_inc_ref(v_inferType_3236_);
lean_dec_ref(v_cache_3235_);
v___x_3237_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3236_, v_a_3190_);
lean_dec_ref(v_inferType_3236_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_cancelTk_x3f_3238_; 
lean_del_object(v___x_3192_);
v_cancelTk_x3f_3238_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3238_) == 1)
{
lean_object* v_val_3239_; uint8_t v___x_3240_; 
v_val_3239_ = lean_ctor_get(v_cancelTk_x3f_3238_, 0);
v___x_3240_ = l_IO_CancelToken_isSet(v_val_3239_);
if (v___x_3240_ == 0)
{
goto v___jp_3194_;
}
else
{
lean_object* v___x_3241_; lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v_a_3190_);
lean_dec_ref(v___x_3172_);
lean_dec_ref(v___x_3167_);
v___x_3241_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
goto v___jp_3194_;
}
}
else
{
lean_object* v_val_3250_; lean_object* v___x_3252_; 
lean_dec(v_a_3190_);
lean_dec_ref(v___x_3172_);
lean_dec_ref(v___x_3167_);
v_val_3250_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_val_3250_);
lean_dec_ref(v___x_3237_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_val_3250_);
v___x_3252_ = v___x_3192_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_val_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
v___jp_3194_:
{
lean_object* v___x_3195_; 
v___x_3195_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3167_, v___x_3172_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec_ref(v___x_3172_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; uint8_t v___x_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
v___x_3197_ = l_Lean_Expr_hasMVar(v_a_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3232_; 
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v___x_3195_, 0);
lean_dec(v_unused_3233_);
v___x_3199_ = v___x_3195_;
v_isShared_3200_ = v_isSharedCheck_3232_;
goto v_resetjp_3198_;
}
else
{
lean_dec(v___x_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3232_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v_cache_3202_; lean_object* v_mctx_3203_; lean_object* v_zetaDeltaFVarIds_3204_; lean_object* v_postponed_3205_; lean_object* v_diag_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3231_; 
v___x_3201_ = lean_st_ref_take(v_a_3022_);
v_cache_3202_ = lean_ctor_get(v___x_3201_, 1);
v_mctx_3203_ = lean_ctor_get(v___x_3201_, 0);
v_zetaDeltaFVarIds_3204_ = lean_ctor_get(v___x_3201_, 2);
v_postponed_3205_ = lean_ctor_get(v___x_3201_, 3);
v_diag_3206_ = lean_ctor_get(v___x_3201_, 4);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3208_ = v___x_3201_;
v_isShared_3209_ = v_isSharedCheck_3231_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_diag_3206_);
lean_inc(v_postponed_3205_);
lean_inc(v_zetaDeltaFVarIds_3204_);
lean_inc(v_cache_3202_);
lean_inc(v_mctx_3203_);
lean_dec(v___x_3201_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3231_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v_inferType_3210_; lean_object* v_funInfo_3211_; lean_object* v_synthInstance_3212_; lean_object* v_whnf_3213_; lean_object* v_defEqTrans_3214_; lean_object* v_defEqPerm_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3230_; 
v_inferType_3210_ = lean_ctor_get(v_cache_3202_, 0);
v_funInfo_3211_ = lean_ctor_get(v_cache_3202_, 1);
v_synthInstance_3212_ = lean_ctor_get(v_cache_3202_, 2);
v_whnf_3213_ = lean_ctor_get(v_cache_3202_, 3);
v_defEqTrans_3214_ = lean_ctor_get(v_cache_3202_, 4);
v_defEqPerm_3215_ = lean_ctor_get(v_cache_3202_, 5);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_cache_3202_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3217_ = v_cache_3202_;
v_isShared_3218_ = v_isSharedCheck_3230_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_defEqPerm_3215_);
lean_inc(v_defEqTrans_3214_);
lean_inc(v_whnf_3213_);
lean_inc(v_synthInstance_3212_);
lean_inc(v_funInfo_3211_);
lean_inc(v_inferType_3210_);
lean_dec(v_cache_3202_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3230_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_inc(v_a_3196_);
v___x_3219_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3210_, v_a_3190_, v_a_3196_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3219_);
v___x_3221_ = v___x_3217_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_funInfo_3211_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_synthInstance_3212_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_whnf_3213_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_defEqTrans_3214_);
lean_ctor_set(v_reuseFailAlloc_3229_, 5, v_defEqPerm_3215_);
v___x_3221_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3223_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3221_);
v___x_3223_ = v___x_3208_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_mctx_3203_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_zetaDeltaFVarIds_3204_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_postponed_3205_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_diag_3206_);
v___x_3223_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3224_ = lean_st_ref_set(v_a_3022_, v___x_3223_);
if (v_isShared_3200_ == 0)
{
v___x_3226_ = v___x_3199_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3196_);
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
}
}
}
else
{
lean_dec(v_a_3196_);
lean_dec(v_a_3190_);
return v___x_3195_;
}
}
else
{
lean_dec(v_a_3190_);
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v___x_3172_);
lean_dec_ref(v___x_3167_);
v_a_3255_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3189_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3189_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_dec_ref(v_e_3020_);
goto v___jp_3173_;
}
}
v___jp_3173_:
{
lean_object* v_cancelTk_x3f_3174_; 
v_cancelTk_x3f_3174_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3174_) == 1)
{
lean_object* v_val_3175_; uint8_t v___x_3176_; 
v_val_3175_ = lean_ctor_get(v_cancelTk_x3f_3174_, 0);
v___x_3176_ = l_IO_CancelToken_isSet(v_val_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; 
v___x_3177_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3167_, v___x_3172_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec_ref(v___x_3172_);
return v___x_3177_;
}
else
{
lean_object* v___x_3178_; lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref(v___x_3172_);
lean_dec_ref(v___x_3167_);
v___x_3178_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3167_, v___x_3172_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec_ref(v___x_3172_);
return v___x_3187_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3263_; 
v_cacheInferType_3263_ = lean_ctor_get_uint8(v_a_3021_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3263_ == 0)
{
goto v___jp_3041_;
}
else
{
uint8_t v___x_3264_; 
v___x_3264_ = l_Lean_Expr_hasMVar(v_e_3020_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; 
lean_inc_ref(v_e_3020_);
v___x_3265_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3330_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3330_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3330_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3310_; lean_object* v_cache_3311_; lean_object* v_inferType_3312_; lean_object* v___x_3313_; 
v___x_3310_ = lean_st_ref_get(v_a_3022_);
v_cache_3311_ = lean_ctor_get(v___x_3310_, 1);
lean_inc_ref(v_cache_3311_);
lean_dec(v___x_3310_);
v_inferType_3312_ = lean_ctor_get(v_cache_3311_, 0);
lean_inc_ref(v_inferType_3312_);
lean_dec_ref(v_cache_3311_);
v___x_3313_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3312_, v_a_3266_);
lean_dec_ref(v_inferType_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_cancelTk_x3f_3314_; 
lean_del_object(v___x_3268_);
v_cancelTk_x3f_3314_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3314_) == 1)
{
lean_object* v_val_3315_; uint8_t v___x_3316_; 
v_val_3315_ = lean_ctor_get(v_cancelTk_x3f_3314_, 0);
v___x_3316_ = l_IO_CancelToken_isSet(v_val_3315_);
if (v___x_3316_ == 0)
{
goto v___jp_3270_;
}
else
{
lean_object* v___x_3317_; lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_a_3266_);
lean_dec_ref(v_e_3020_);
v___x_3317_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
goto v___jp_3270_;
}
}
else
{
lean_object* v_val_3326_; lean_object* v___x_3328_; 
lean_dec(v_a_3266_);
lean_dec_ref(v_e_3020_);
v_val_3326_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_val_3326_);
lean_dec_ref(v___x_3313_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v_val_3326_);
v___x_3328_ = v___x_3268_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_val_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
v___jp_3270_:
{
lean_object* v___x_3271_; 
v___x_3271_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; uint8_t v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
v___x_3273_ = l_Lean_Expr_hasMVar(v_a_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3308_; 
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; 
v_unused_3309_ = lean_ctor_get(v___x_3271_, 0);
lean_dec(v_unused_3309_);
v___x_3275_ = v___x_3271_;
v_isShared_3276_ = v_isSharedCheck_3308_;
goto v_resetjp_3274_;
}
else
{
lean_dec(v___x_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3308_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v_cache_3278_; lean_object* v_mctx_3279_; lean_object* v_zetaDeltaFVarIds_3280_; lean_object* v_postponed_3281_; lean_object* v_diag_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3307_; 
v___x_3277_ = lean_st_ref_take(v_a_3022_);
v_cache_3278_ = lean_ctor_get(v___x_3277_, 1);
v_mctx_3279_ = lean_ctor_get(v___x_3277_, 0);
v_zetaDeltaFVarIds_3280_ = lean_ctor_get(v___x_3277_, 2);
v_postponed_3281_ = lean_ctor_get(v___x_3277_, 3);
v_diag_3282_ = lean_ctor_get(v___x_3277_, 4);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3284_ = v___x_3277_;
v_isShared_3285_ = v_isSharedCheck_3307_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_diag_3282_);
lean_inc(v_postponed_3281_);
lean_inc(v_zetaDeltaFVarIds_3280_);
lean_inc(v_cache_3278_);
lean_inc(v_mctx_3279_);
lean_dec(v___x_3277_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3307_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v_inferType_3286_; lean_object* v_funInfo_3287_; lean_object* v_synthInstance_3288_; lean_object* v_whnf_3289_; lean_object* v_defEqTrans_3290_; lean_object* v_defEqPerm_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3306_; 
v_inferType_3286_ = lean_ctor_get(v_cache_3278_, 0);
v_funInfo_3287_ = lean_ctor_get(v_cache_3278_, 1);
v_synthInstance_3288_ = lean_ctor_get(v_cache_3278_, 2);
v_whnf_3289_ = lean_ctor_get(v_cache_3278_, 3);
v_defEqTrans_3290_ = lean_ctor_get(v_cache_3278_, 4);
v_defEqPerm_3291_ = lean_ctor_get(v_cache_3278_, 5);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_cache_3278_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3293_ = v_cache_3278_;
v_isShared_3294_ = v_isSharedCheck_3306_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_defEqPerm_3291_);
lean_inc(v_defEqTrans_3290_);
lean_inc(v_whnf_3289_);
lean_inc(v_synthInstance_3288_);
lean_inc(v_funInfo_3287_);
lean_inc(v_inferType_3286_);
lean_dec(v_cache_3278_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3306_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; lean_object* v___x_3297_; 
lean_inc(v_a_3272_);
v___x_3295_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3286_, v_a_3266_, v_a_3272_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3295_);
v___x_3297_ = v___x_3293_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_funInfo_3287_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_synthInstance_3288_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_whnf_3289_);
lean_ctor_set(v_reuseFailAlloc_3305_, 4, v_defEqTrans_3290_);
lean_ctor_set(v_reuseFailAlloc_3305_, 5, v_defEqPerm_3291_);
v___x_3297_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3297_);
v___x_3299_ = v___x_3284_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_mctx_3279_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_zetaDeltaFVarIds_3280_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_postponed_3281_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_diag_3282_);
v___x_3299_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = lean_st_ref_set(v_a_3022_, v___x_3299_);
if (v_isShared_3276_ == 0)
{
v___x_3302_ = v___x_3275_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3272_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3272_);
lean_dec(v_a_3266_);
return v___x_3271_;
}
}
else
{
lean_dec(v_a_3266_);
return v___x_3271_;
}
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v_e_3020_);
v_a_3331_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3265_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3265_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
goto v___jp_3041_;
}
}
}
case 9:
{
lean_object* v_a_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_a_3339_ = lean_ctor_get(v_e_3020_, 0);
lean_inc_ref(v_a_3339_);
lean_dec_ref(v_e_3020_);
v___x_3340_ = l_Lean_Literal_type(v_a_3339_);
lean_dec_ref(v_a_3339_);
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
case 10:
{
lean_object* v_expr_3342_; 
v_expr_3342_ = lean_ctor_get(v_e_3020_, 1);
lean_inc_ref(v_expr_3342_);
lean_dec_ref(v_e_3020_);
v_e_3020_ = v_expr_3342_;
goto _start;
}
case 11:
{
lean_object* v_typeName_3344_; lean_object* v_idx_3345_; lean_object* v_struct_3346_; uint8_t v_cacheInferType_3362_; 
v_typeName_3344_ = lean_ctor_get(v_e_3020_, 0);
lean_inc(v_typeName_3344_);
v_idx_3345_ = lean_ctor_get(v_e_3020_, 1);
lean_inc(v_idx_3345_);
v_struct_3346_ = lean_ctor_get(v_e_3020_, 2);
lean_inc_ref(v_struct_3346_);
v_cacheInferType_3362_ = lean_ctor_get_uint8(v_a_3021_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3362_ == 0)
{
lean_dec_ref(v_e_3020_);
goto v___jp_3347_;
}
else
{
uint8_t v___x_3363_; 
v___x_3363_ = l_Lean_Expr_hasMVar(v_e_3020_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3429_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3429_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3429_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3409_; lean_object* v_cache_3410_; lean_object* v_inferType_3411_; lean_object* v___x_3412_; 
v___x_3409_ = lean_st_ref_get(v_a_3022_);
v_cache_3410_ = lean_ctor_get(v___x_3409_, 1);
lean_inc_ref(v_cache_3410_);
lean_dec(v___x_3409_);
v_inferType_3411_ = lean_ctor_get(v_cache_3410_, 0);
lean_inc_ref(v_inferType_3411_);
lean_dec_ref(v_cache_3410_);
v___x_3412_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3411_, v_a_3365_);
lean_dec_ref(v_inferType_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_cancelTk_x3f_3413_; 
lean_del_object(v___x_3367_);
v_cancelTk_x3f_3413_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3413_) == 1)
{
lean_object* v_val_3414_; uint8_t v___x_3415_; 
v_val_3414_ = lean_ctor_get(v_cancelTk_x3f_3413_, 0);
v___x_3415_ = l_IO_CancelToken_isSet(v_val_3414_);
if (v___x_3415_ == 0)
{
goto v___jp_3369_;
}
else
{
lean_object* v___x_3416_; lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec(v_a_3365_);
lean_dec_ref(v_struct_3346_);
lean_dec(v_idx_3345_);
lean_dec(v_typeName_3344_);
v___x_3416_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
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
else
{
goto v___jp_3369_;
}
}
else
{
lean_object* v_val_3425_; lean_object* v___x_3427_; 
lean_dec(v_a_3365_);
lean_dec_ref(v_struct_3346_);
lean_dec(v_idx_3345_);
lean_dec(v_typeName_3344_);
v_val_3425_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_val_3425_);
lean_dec_ref(v___x_3412_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v_val_3425_);
v___x_3427_ = v___x_3367_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_val_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
v___jp_3369_:
{
lean_object* v___x_3370_; 
v___x_3370_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3344_, v_idx_3345_, v_struct_3346_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; uint8_t v___x_3372_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
v___x_3372_ = l_Lean_Expr_hasMVar(v_a_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3407_; 
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v___x_3370_, 0);
lean_dec(v_unused_3408_);
v___x_3374_ = v___x_3370_;
v_isShared_3375_ = v_isSharedCheck_3407_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v___x_3370_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3407_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v_cache_3377_; lean_object* v_mctx_3378_; lean_object* v_zetaDeltaFVarIds_3379_; lean_object* v_postponed_3380_; lean_object* v_diag_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3406_; 
v___x_3376_ = lean_st_ref_take(v_a_3022_);
v_cache_3377_ = lean_ctor_get(v___x_3376_, 1);
v_mctx_3378_ = lean_ctor_get(v___x_3376_, 0);
v_zetaDeltaFVarIds_3379_ = lean_ctor_get(v___x_3376_, 2);
v_postponed_3380_ = lean_ctor_get(v___x_3376_, 3);
v_diag_3381_ = lean_ctor_get(v___x_3376_, 4);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3383_ = v___x_3376_;
v_isShared_3384_ = v_isSharedCheck_3406_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_diag_3381_);
lean_inc(v_postponed_3380_);
lean_inc(v_zetaDeltaFVarIds_3379_);
lean_inc(v_cache_3377_);
lean_inc(v_mctx_3378_);
lean_dec(v___x_3376_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3406_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_inferType_3385_; lean_object* v_funInfo_3386_; lean_object* v_synthInstance_3387_; lean_object* v_whnf_3388_; lean_object* v_defEqTrans_3389_; lean_object* v_defEqPerm_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3405_; 
v_inferType_3385_ = lean_ctor_get(v_cache_3377_, 0);
v_funInfo_3386_ = lean_ctor_get(v_cache_3377_, 1);
v_synthInstance_3387_ = lean_ctor_get(v_cache_3377_, 2);
v_whnf_3388_ = lean_ctor_get(v_cache_3377_, 3);
v_defEqTrans_3389_ = lean_ctor_get(v_cache_3377_, 4);
v_defEqPerm_3390_ = lean_ctor_get(v_cache_3377_, 5);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_cache_3377_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3392_ = v_cache_3377_;
v_isShared_3393_ = v_isSharedCheck_3405_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_defEqPerm_3390_);
lean_inc(v_defEqTrans_3389_);
lean_inc(v_whnf_3388_);
lean_inc(v_synthInstance_3387_);
lean_inc(v_funInfo_3386_);
lean_inc(v_inferType_3385_);
lean_dec(v_cache_3377_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3405_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___x_3396_; 
lean_inc(v_a_3371_);
v___x_3394_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3385_, v_a_3365_, v_a_3371_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3394_);
v___x_3396_ = v___x_3392_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_funInfo_3386_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_synthInstance_3387_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_whnf_3388_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v_defEqTrans_3389_);
lean_ctor_set(v_reuseFailAlloc_3404_, 5, v_defEqPerm_3390_);
v___x_3396_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 1, v___x_3396_);
v___x_3398_ = v___x_3383_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_mctx_3378_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3403_, 2, v_zetaDeltaFVarIds_3379_);
lean_ctor_set(v_reuseFailAlloc_3403_, 3, v_postponed_3380_);
lean_ctor_set(v_reuseFailAlloc_3403_, 4, v_diag_3381_);
v___x_3398_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_st_ref_set(v_a_3022_, v___x_3398_);
if (v_isShared_3375_ == 0)
{
v___x_3401_ = v___x_3374_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3371_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3371_);
lean_dec(v_a_3365_);
return v___x_3370_;
}
}
else
{
lean_dec(v_a_3365_);
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_struct_3346_);
lean_dec(v_idx_3345_);
lean_dec(v_typeName_3344_);
v_a_3430_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3364_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3364_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_dec_ref(v_e_3020_);
goto v___jp_3347_;
}
}
v___jp_3347_:
{
lean_object* v_cancelTk_x3f_3348_; 
v_cancelTk_x3f_3348_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3348_) == 1)
{
lean_object* v_val_3349_; uint8_t v___x_3350_; 
v_val_3349_ = lean_ctor_get(v_cancelTk_x3f_3348_, 0);
v___x_3350_ = l_IO_CancelToken_isSet(v_val_3349_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; 
v___x_3351_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3344_, v_idx_3345_, v_struct_3346_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3351_;
}
else
{
lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v_struct_3346_);
lean_dec(v_idx_3345_);
lean_dec(v_typeName_3344_);
v___x_3352_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v___x_3361_; 
v___x_3361_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3344_, v_idx_3345_, v_struct_3346_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3361_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3438_; 
v_cacheInferType_3438_ = lean_ctor_get_uint8(v_a_3021_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3438_ == 0)
{
goto v___jp_3026_;
}
else
{
uint8_t v___x_3439_; 
v___x_3439_ = l_Lean_Expr_hasMVar(v_e_3020_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
lean_inc_ref(v_e_3020_);
v___x_3440_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3505_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3505_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3505_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3485_; lean_object* v_cache_3486_; lean_object* v_inferType_3487_; lean_object* v___x_3488_; 
v___x_3485_ = lean_st_ref_get(v_a_3022_);
v_cache_3486_ = lean_ctor_get(v___x_3485_, 1);
lean_inc_ref(v_cache_3486_);
lean_dec(v___x_3485_);
v_inferType_3487_ = lean_ctor_get(v_cache_3486_, 0);
lean_inc_ref(v_inferType_3487_);
lean_dec_ref(v_cache_3486_);
v___x_3488_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_inferType_3487_, v_a_3441_);
lean_dec_ref(v_inferType_3487_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_cancelTk_x3f_3489_; 
lean_del_object(v___x_3443_);
v_cancelTk_x3f_3489_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3489_) == 1)
{
lean_object* v_val_3490_; uint8_t v___x_3491_; 
v_val_3490_ = lean_ctor_get(v_cancelTk_x3f_3489_, 0);
v___x_3491_ = l_IO_CancelToken_isSet(v_val_3490_);
if (v___x_3491_ == 0)
{
goto v___jp_3445_;
}
else
{
lean_object* v___x_3492_; lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3020_);
v___x_3492_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
else
{
goto v___jp_3445_;
}
}
else
{
lean_object* v_val_3501_; lean_object* v___x_3503_; 
lean_dec(v_a_3441_);
lean_dec_ref(v_e_3020_);
v_val_3501_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_val_3501_);
lean_dec_ref(v___x_3488_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v_val_3501_);
v___x_3503_ = v___x_3443_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_val_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
v___jp_3445_:
{
lean_object* v___x_3446_; 
v___x_3446_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; uint8_t v___x_3448_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
v___x_3448_ = l_Lean_Expr_hasMVar(v_a_3447_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3483_; 
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v___x_3446_, 0);
lean_dec(v_unused_3484_);
v___x_3450_ = v___x_3446_;
v_isShared_3451_ = v_isSharedCheck_3483_;
goto v_resetjp_3449_;
}
else
{
lean_dec(v___x_3446_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3483_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v_cache_3453_; lean_object* v_mctx_3454_; lean_object* v_zetaDeltaFVarIds_3455_; lean_object* v_postponed_3456_; lean_object* v_diag_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3482_; 
v___x_3452_ = lean_st_ref_take(v_a_3022_);
v_cache_3453_ = lean_ctor_get(v___x_3452_, 1);
v_mctx_3454_ = lean_ctor_get(v___x_3452_, 0);
v_zetaDeltaFVarIds_3455_ = lean_ctor_get(v___x_3452_, 2);
v_postponed_3456_ = lean_ctor_get(v___x_3452_, 3);
v_diag_3457_ = lean_ctor_get(v___x_3452_, 4);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3459_ = v___x_3452_;
v_isShared_3460_ = v_isSharedCheck_3482_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_diag_3457_);
lean_inc(v_postponed_3456_);
lean_inc(v_zetaDeltaFVarIds_3455_);
lean_inc(v_cache_3453_);
lean_inc(v_mctx_3454_);
lean_dec(v___x_3452_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3482_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_inferType_3461_; lean_object* v_funInfo_3462_; lean_object* v_synthInstance_3463_; lean_object* v_whnf_3464_; lean_object* v_defEqTrans_3465_; lean_object* v_defEqPerm_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3481_; 
v_inferType_3461_ = lean_ctor_get(v_cache_3453_, 0);
v_funInfo_3462_ = lean_ctor_get(v_cache_3453_, 1);
v_synthInstance_3463_ = lean_ctor_get(v_cache_3453_, 2);
v_whnf_3464_ = lean_ctor_get(v_cache_3453_, 3);
v_defEqTrans_3465_ = lean_ctor_get(v_cache_3453_, 4);
v_defEqPerm_3466_ = lean_ctor_get(v_cache_3453_, 5);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_cache_3453_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3468_ = v_cache_3453_;
v_isShared_3469_ = v_isSharedCheck_3481_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_defEqPerm_3466_);
lean_inc(v_defEqTrans_3465_);
lean_inc(v_whnf_3464_);
lean_inc(v_synthInstance_3463_);
lean_inc(v_funInfo_3462_);
lean_inc(v_inferType_3461_);
lean_dec(v_cache_3453_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3481_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
lean_inc(v_a_3447_);
v___x_3470_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3461_, v_a_3441_, v_a_3447_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3470_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_funInfo_3462_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_synthInstance_3463_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_whnf_3464_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_defEqTrans_3465_);
lean_ctor_set(v_reuseFailAlloc_3480_, 5, v_defEqPerm_3466_);
v___x_3472_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3474_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 1, v___x_3472_);
v___x_3474_ = v___x_3459_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_mctx_3454_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_zetaDeltaFVarIds_3455_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_postponed_3456_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_diag_3457_);
v___x_3474_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_st_ref_set(v_a_3022_, v___x_3474_);
if (v_isShared_3451_ == 0)
{
v___x_3477_ = v___x_3450_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3447_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
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
lean_dec(v_a_3441_);
return v___x_3446_;
}
}
else
{
lean_dec(v_a_3441_);
return v___x_3446_;
}
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_dec_ref(v_e_3020_);
v_a_3506_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3440_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3440_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
goto v___jp_3026_;
}
}
}
}
v___jp_3026_:
{
lean_object* v_cancelTk_x3f_3027_; 
v_cancelTk_x3f_3027_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3027_) == 1)
{
lean_object* v_val_3028_; uint8_t v___x_3029_; 
v_val_3028_ = lean_ctor_get(v_cancelTk_x3f_3027_, 0);
v___x_3029_ = l_IO_CancelToken_isSet(v_val_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_e_3020_);
v___x_3031_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg();
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3040_;
}
}
v___jp_3041_:
{
lean_object* v_cancelTk_x3f_3042_; 
v_cancelTk_x3f_3042_ = lean_ctor_get(v_a_3023_, 12);
if (lean_obj_tag(v_cancelTk_x3f_3042_) == 1)
{
lean_object* v_val_3043_; uint8_t v___x_3044_; 
v_val_3043_ = lean_ctor_get(v_cancelTk_x3f_3042_, 0);
v___x_3044_ = l_IO_CancelToken_isSet(v_val_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
v___x_3045_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v_e_3020_);
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
v___x_3055_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
return v___x_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3521_, lean_object* v_x_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3522_, v_x_3523_, v_x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(lean_object* v_00_u03b2_3526_, lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___redArg(v_x_3527_, v_x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2___boxed(lean_object* v_00_u03b2_3530_, lean_object* v_x_3531_, lean_object* v_x_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2(v_00_u03b2_3530_, v_x_3531_, v_x_3532_);
lean_dec_ref(v_x_3532_);
lean_dec_ref(v_x_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(lean_object* v_00_u03b2_3534_, lean_object* v_x_3535_, size_t v_x_3536_, size_t v_x_3537_, lean_object* v_x_3538_, lean_object* v_x_3539_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___redArg(v_x_3535_, v_x_3536_, v_x_3537_, v_x_3538_, v_x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3541_, lean_object* v_x_3542_, lean_object* v_x_3543_, lean_object* v_x_3544_, lean_object* v_x_3545_, lean_object* v_x_3546_){
_start:
{
size_t v_x_4029__boxed_3547_; size_t v_x_4030__boxed_3548_; lean_object* v_res_3549_; 
v_x_4029__boxed_3547_ = lean_unbox_usize(v_x_3543_);
lean_dec(v_x_3543_);
v_x_4030__boxed_3548_ = lean_unbox_usize(v_x_3544_);
lean_dec(v_x_3544_);
v_res_3549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1(v_00_u03b2_3541_, v_x_3542_, v_x_4029__boxed_3547_, v_x_4030__boxed_3548_, v_x_3545_, v_x_3546_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(lean_object* v_00_u03b2_3550_, lean_object* v_x_3551_, size_t v_x_3552_, lean_object* v_x_3553_){
_start:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___redArg(v_x_3551_, v_x_3552_, v_x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_, lean_object* v_x_3558_){
_start:
{
size_t v_x_4046__boxed_3559_; lean_object* v_res_3560_; 
v_x_4046__boxed_3559_ = lean_unbox_usize(v_x_3557_);
lean_dec(v_x_3557_);
v_res_3560_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3(v_00_u03b2_3555_, v_x_3556_, v_x_4046__boxed_3559_, v_x_3558_);
lean_dec_ref(v_x_3558_);
lean_dec_ref(v_x_3556_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3561_, lean_object* v_n_3562_, lean_object* v_k_3563_, lean_object* v_v_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2___redArg(v_n_3562_, v_k_3563_, v_v_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_3566_, size_t v_depth_3567_, lean_object* v_keys_3568_, lean_object* v_vals_3569_, lean_object* v_heq_3570_, lean_object* v_i_3571_, lean_object* v_entries_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___redArg(v_depth_3567_, v_keys_3568_, v_vals_3569_, v_i_3571_, v_entries_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3574_, lean_object* v_depth_3575_, lean_object* v_keys_3576_, lean_object* v_vals_3577_, lean_object* v_heq_3578_, lean_object* v_i_3579_, lean_object* v_entries_3580_){
_start:
{
size_t v_depth_boxed_3581_; lean_object* v_res_3582_; 
v_depth_boxed_3581_ = lean_unbox_usize(v_depth_3575_);
lean_dec(v_depth_3575_);
v_res_3582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__3(v_00_u03b2_3574_, v_depth_boxed_3581_, v_keys_3576_, v_vals_3577_, v_heq_3578_, v_i_3579_, v_entries_3580_);
lean_dec_ref(v_vals_3577_);
lean_dec_ref(v_keys_3576_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_3583_, lean_object* v_keys_3584_, lean_object* v_vals_3585_, lean_object* v_heq_3586_, lean_object* v_i_3587_, lean_object* v_k_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___redArg(v_keys_3584_, v_vals_3585_, v_i_3587_, v_k_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3590_, lean_object* v_keys_3591_, lean_object* v_vals_3592_, lean_object* v_heq_3593_, lean_object* v_i_3594_, lean_object* v_k_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__2_spec__3_spec__6(v_00_u03b2_3590_, v_keys_3591_, v_vals_3592_, v_heq_3593_, v_i_3594_, v_k_3595_);
lean_dec_ref(v_k_3595_);
lean_dec_ref(v_vals_3592_);
lean_dec_ref(v_keys_3591_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3597_, lean_object* v_x_3598_, lean_object* v_x_3599_, lean_object* v_x_3600_, lean_object* v_x_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__1_spec__2_spec__4___redArg(v_x_3598_, v_x_3599_, v_x_3600_, v_x_3601_);
return v___x_3602_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = l_Lean_maxRecDepthErrorMessage;
v___x_3609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
return v___x_3609_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3611_ = l_Lean_MessageData_ofFormat(v___x_3610_);
return v___x_3611_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3613_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3614_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v___x_3612_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3615_){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v_ref_3615_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3620_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3623_, lean_object* v_ref_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3624_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3631_, lean_object* v_ref_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3631_, v_ref_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; uint8_t v___y_3651_; lean_object* v___y_3652_; uint8_t v___y_3653_; uint8_t v___y_3654_; uint8_t v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3686_; uint8_t v___y_3687_; lean_object* v_fileName_3758_; lean_object* v_fileMap_3759_; lean_object* v_options_3760_; lean_object* v_currRecDepth_3761_; lean_object* v_maxRecDepth_3762_; lean_object* v_ref_3763_; lean_object* v_currNamespace_3764_; lean_object* v_openDecls_3765_; lean_object* v_initHeartbeats_3766_; lean_object* v_maxHeartbeats_3767_; lean_object* v_quotContext_3768_; lean_object* v_currMacroScope_3769_; uint8_t v_diag_3770_; lean_object* v_cancelTk_x3f_3771_; uint8_t v_suppressElabErrors_3772_; lean_object* v_inheritedTraceOptions_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3791_; 
v_fileName_3758_ = lean_ctor_get(v_a_3642_, 0);
v_fileMap_3759_ = lean_ctor_get(v_a_3642_, 1);
v_options_3760_ = lean_ctor_get(v_a_3642_, 2);
v_currRecDepth_3761_ = lean_ctor_get(v_a_3642_, 3);
v_maxRecDepth_3762_ = lean_ctor_get(v_a_3642_, 4);
v_ref_3763_ = lean_ctor_get(v_a_3642_, 5);
v_currNamespace_3764_ = lean_ctor_get(v_a_3642_, 6);
v_openDecls_3765_ = lean_ctor_get(v_a_3642_, 7);
v_initHeartbeats_3766_ = lean_ctor_get(v_a_3642_, 8);
v_maxHeartbeats_3767_ = lean_ctor_get(v_a_3642_, 9);
v_quotContext_3768_ = lean_ctor_get(v_a_3642_, 10);
v_currMacroScope_3769_ = lean_ctor_get(v_a_3642_, 11);
v_diag_3770_ = lean_ctor_get_uint8(v_a_3642_, sizeof(void*)*14);
v_cancelTk_x3f_3771_ = lean_ctor_get(v_a_3642_, 12);
v_suppressElabErrors_3772_ = lean_ctor_get_uint8(v_a_3642_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3773_ = lean_ctor_get(v_a_3642_, 13);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3775_ = v_a_3642_;
v_isShared_3776_ = v_isSharedCheck_3791_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_inheritedTraceOptions_3773_);
lean_inc(v_cancelTk_x3f_3771_);
lean_inc(v_currMacroScope_3769_);
lean_inc(v_quotContext_3768_);
lean_inc(v_maxHeartbeats_3767_);
lean_inc(v_initHeartbeats_3766_);
lean_inc(v_openDecls_3765_);
lean_inc(v_currNamespace_3764_);
lean_inc(v_ref_3763_);
lean_inc(v_maxRecDepth_3762_);
lean_inc(v_currRecDepth_3761_);
lean_inc(v_options_3760_);
lean_inc(v_fileMap_3759_);
lean_inc(v_fileName_3758_);
lean_dec(v_a_3642_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3791_;
goto v_resetjp_3774_;
}
v___jp_3645_:
{
lean_object* v___x_3658_; uint8_t v_foApprox_3659_; uint8_t v_ctxApprox_3660_; uint8_t v_quasiPatternApprox_3661_; uint8_t v_constApprox_3662_; uint8_t v_isDefEqStuckEx_3663_; uint8_t v_unificationHints_3664_; uint8_t v_proofIrrelevance_3665_; uint8_t v_assignSyntheticOpaque_3666_; uint8_t v_offsetCnstrs_3667_; uint8_t v_transparency_3668_; uint8_t v_univApprox_3669_; uint8_t v_zetaUnused_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3684_; 
v___x_3658_ = l_Lean_Meta_Context_config(v___y_3657_);
lean_dec_ref(v___y_3657_);
v_foApprox_3659_ = lean_ctor_get_uint8(v___x_3658_, 0);
v_ctxApprox_3660_ = lean_ctor_get_uint8(v___x_3658_, 1);
v_quasiPatternApprox_3661_ = lean_ctor_get_uint8(v___x_3658_, 2);
v_constApprox_3662_ = lean_ctor_get_uint8(v___x_3658_, 3);
v_isDefEqStuckEx_3663_ = lean_ctor_get_uint8(v___x_3658_, 4);
v_unificationHints_3664_ = lean_ctor_get_uint8(v___x_3658_, 5);
v_proofIrrelevance_3665_ = lean_ctor_get_uint8(v___x_3658_, 6);
v_assignSyntheticOpaque_3666_ = lean_ctor_get_uint8(v___x_3658_, 7);
v_offsetCnstrs_3667_ = lean_ctor_get_uint8(v___x_3658_, 8);
v_transparency_3668_ = lean_ctor_get_uint8(v___x_3658_, 9);
v_univApprox_3669_ = lean_ctor_get_uint8(v___x_3658_, 11);
v_zetaUnused_3670_ = lean_ctor_get_uint8(v___x_3658_, 17);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3672_ = v___x_3658_;
v_isShared_3673_ = v_isSharedCheck_3684_;
goto v_resetjp_3671_;
}
else
{
lean_dec(v___x_3658_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3684_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
uint8_t v___x_3674_; uint8_t v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3678_; 
v___x_3674_ = 1;
v___x_3675_ = 0;
v___x_3676_ = 2;
if (v_isShared_3673_ == 0)
{
v___x_3678_ = v___x_3672_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 0, v_foApprox_3659_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 1, v_ctxApprox_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 2, v_quasiPatternApprox_3661_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 3, v_constApprox_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 4, v_isDefEqStuckEx_3663_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 5, v_unificationHints_3664_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 6, v_proofIrrelevance_3665_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 7, v_assignSyntheticOpaque_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 8, v_offsetCnstrs_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 9, v_transparency_3668_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 11, v_univApprox_3669_);
lean_ctor_set_uint8(v_reuseFailAlloc_3683_, 17, v_zetaUnused_3670_);
v___x_3678_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
uint64_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_ctor_set_uint8(v___x_3678_, 10, v___x_3675_);
lean_ctor_set_uint8(v___x_3678_, 12, v___x_3674_);
lean_ctor_set_uint8(v___x_3678_, 13, v___x_3674_);
lean_ctor_set_uint8(v___x_3678_, 14, v___x_3676_);
lean_ctor_set_uint8(v___x_3678_, 15, v___x_3674_);
lean_ctor_set_uint8(v___x_3678_, 16, v___x_3674_);
lean_ctor_set_uint8(v___x_3678_, 18, v___x_3674_);
v___x_3679_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3678_);
v___x_3680_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set_uint64(v___x_3680_, sizeof(void*)*1, v___x_3679_);
v___x_3681_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___y_3650_);
lean_ctor_set(v___x_3681_, 2, v___y_3647_);
lean_ctor_set(v___x_3681_, 3, v___y_3652_);
lean_ctor_set(v___x_3681_, 4, v___y_3646_);
lean_ctor_set(v___x_3681_, 5, v___y_3649_);
lean_ctor_set(v___x_3681_, 6, v___y_3648_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*7, v___y_3655_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*7 + 1, v___y_3653_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*7 + 2, v___y_3654_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*7 + 3, v___y_3651_);
v___x_3682_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3639_, v___x_3681_, v_a_3641_, v___y_3656_, v_a_3643_);
lean_dec(v_a_3643_);
lean_dec_ref(v___y_3656_);
lean_dec(v_a_3641_);
lean_dec_ref(v___x_3681_);
return v___x_3682_;
}
}
}
v___jp_3685_:
{
lean_object* v___x_3688_; uint8_t v_foApprox_3689_; uint8_t v_ctxApprox_3690_; uint8_t v_quasiPatternApprox_3691_; uint8_t v_constApprox_3692_; uint8_t v_isDefEqStuckEx_3693_; uint8_t v_unificationHints_3694_; uint8_t v_proofIrrelevance_3695_; uint8_t v_assignSyntheticOpaque_3696_; uint8_t v_offsetCnstrs_3697_; uint8_t v_etaStruct_3698_; uint8_t v_univApprox_3699_; uint8_t v_iota_3700_; uint8_t v_beta_3701_; uint8_t v_proj_3702_; uint8_t v_zeta_3703_; uint8_t v_zetaDelta_3704_; uint8_t v_zetaUnused_3705_; uint8_t v_zetaHave_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3757_; 
v___x_3688_ = l_Lean_Meta_Context_config(v_a_3640_);
v_foApprox_3689_ = lean_ctor_get_uint8(v___x_3688_, 0);
v_ctxApprox_3690_ = lean_ctor_get_uint8(v___x_3688_, 1);
v_quasiPatternApprox_3691_ = lean_ctor_get_uint8(v___x_3688_, 2);
v_constApprox_3692_ = lean_ctor_get_uint8(v___x_3688_, 3);
v_isDefEqStuckEx_3693_ = lean_ctor_get_uint8(v___x_3688_, 4);
v_unificationHints_3694_ = lean_ctor_get_uint8(v___x_3688_, 5);
v_proofIrrelevance_3695_ = lean_ctor_get_uint8(v___x_3688_, 6);
v_assignSyntheticOpaque_3696_ = lean_ctor_get_uint8(v___x_3688_, 7);
v_offsetCnstrs_3697_ = lean_ctor_get_uint8(v___x_3688_, 8);
v_etaStruct_3698_ = lean_ctor_get_uint8(v___x_3688_, 10);
v_univApprox_3699_ = lean_ctor_get_uint8(v___x_3688_, 11);
v_iota_3700_ = lean_ctor_get_uint8(v___x_3688_, 12);
v_beta_3701_ = lean_ctor_get_uint8(v___x_3688_, 13);
v_proj_3702_ = lean_ctor_get_uint8(v___x_3688_, 14);
v_zeta_3703_ = lean_ctor_get_uint8(v___x_3688_, 15);
v_zetaDelta_3704_ = lean_ctor_get_uint8(v___x_3688_, 16);
v_zetaUnused_3705_ = lean_ctor_get_uint8(v___x_3688_, 17);
v_zetaHave_3706_ = lean_ctor_get_uint8(v___x_3688_, 18);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3708_ = v___x_3688_;
v_isShared_3709_ = v_isSharedCheck_3757_;
goto v_resetjp_3707_;
}
else
{
lean_dec(v___x_3688_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3757_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
uint8_t v_trackZetaDelta_3710_; lean_object* v_zetaDeltaSet_3711_; lean_object* v_lctx_3712_; lean_object* v_localInstances_3713_; lean_object* v_defEqCtx_x3f_3714_; lean_object* v_synthPendingDepth_3715_; lean_object* v_canUnfold_x3f_3716_; uint8_t v_univApprox_3717_; uint8_t v_inTypeClassResolution_3718_; uint8_t v_cacheInferType_3719_; lean_object* v_config_3721_; 
v_trackZetaDelta_3710_ = lean_ctor_get_uint8(v_a_3640_, sizeof(void*)*7);
v_zetaDeltaSet_3711_ = lean_ctor_get(v_a_3640_, 1);
lean_inc(v_zetaDeltaSet_3711_);
v_lctx_3712_ = lean_ctor_get(v_a_3640_, 2);
lean_inc_ref(v_lctx_3712_);
v_localInstances_3713_ = lean_ctor_get(v_a_3640_, 3);
lean_inc_ref(v_localInstances_3713_);
v_defEqCtx_x3f_3714_ = lean_ctor_get(v_a_3640_, 4);
lean_inc(v_defEqCtx_x3f_3714_);
v_synthPendingDepth_3715_ = lean_ctor_get(v_a_3640_, 5);
lean_inc(v_synthPendingDepth_3715_);
v_canUnfold_x3f_3716_ = lean_ctor_get(v_a_3640_, 6);
lean_inc(v_canUnfold_x3f_3716_);
v_univApprox_3717_ = lean_ctor_get_uint8(v_a_3640_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3718_ = lean_ctor_get_uint8(v_a_3640_, sizeof(void*)*7 + 2);
v_cacheInferType_3719_ = lean_ctor_get_uint8(v_a_3640_, sizeof(void*)*7 + 3);
if (v_isShared_3709_ == 0)
{
v_config_3721_ = v___x_3708_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 0, v_foApprox_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 1, v_ctxApprox_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 2, v_quasiPatternApprox_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 3, v_constApprox_3692_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 4, v_isDefEqStuckEx_3693_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 5, v_unificationHints_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 6, v_proofIrrelevance_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 7, v_assignSyntheticOpaque_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 8, v_offsetCnstrs_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 10, v_etaStruct_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 11, v_univApprox_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 12, v_iota_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 13, v_beta_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 14, v_proj_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 15, v_zeta_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 16, v_zetaDelta_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 17, v_zetaUnused_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3756_, 18, v_zetaHave_3706_);
v_config_3721_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
uint64_t v___x_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3748_; 
lean_ctor_set_uint8(v_config_3721_, 9, v___y_3687_);
v___x_3722_ = l_Lean_Meta_Context_configKey(v_a_3640_);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_a_3640_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; lean_object* v_unused_3750_; lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; lean_object* v_unused_3755_; 
v_unused_3749_ = lean_ctor_get(v_a_3640_, 6);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_a_3640_, 5);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_a_3640_, 4);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_a_3640_, 3);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_a_3640_, 2);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_a_3640_, 1);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_a_3640_, 0);
lean_dec(v_unused_3755_);
v___x_3724_ = v_a_3640_;
v_isShared_3725_ = v_isSharedCheck_3748_;
goto v_resetjp_3723_;
}
else
{
lean_dec(v_a_3640_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3748_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
uint64_t v___x_3726_; uint64_t v___x_3727_; uint64_t v___x_3728_; uint64_t v___x_3729_; uint64_t v_key_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3726_ = 2ULL;
v___x_3727_ = lean_uint64_shift_right(v___x_3722_, v___x_3726_);
v___x_3728_ = lean_uint64_shift_left(v___x_3727_, v___x_3726_);
v___x_3729_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3687_);
v_key_3730_ = lean_uint64_lor(v___x_3728_, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3731_, 0, v_config_3721_);
lean_ctor_set_uint64(v___x_3731_, sizeof(void*)*1, v_key_3730_);
lean_inc(v_canUnfold_x3f_3716_);
lean_inc(v_synthPendingDepth_3715_);
lean_inc(v_defEqCtx_x3f_3714_);
lean_inc_ref(v_localInstances_3713_);
lean_inc_ref(v_lctx_3712_);
lean_inc(v_zetaDeltaSet_3711_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3731_);
v___x_3733_ = v___x_3724_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_zetaDeltaSet_3711_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_lctx_3712_);
lean_ctor_set(v_reuseFailAlloc_3747_, 3, v_localInstances_3713_);
lean_ctor_set(v_reuseFailAlloc_3747_, 4, v_defEqCtx_x3f_3714_);
lean_ctor_set(v_reuseFailAlloc_3747_, 5, v_synthPendingDepth_3715_);
lean_ctor_set(v_reuseFailAlloc_3747_, 6, v_canUnfold_x3f_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7, v_trackZetaDelta_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7 + 1, v_univApprox_3717_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3718_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7 + 3, v_cacheInferType_3719_);
v___x_3733_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3734_; uint8_t v_beta_3735_; 
v___x_3734_ = l_Lean_Meta_Context_config(v___x_3733_);
v_beta_3735_ = lean_ctor_get_uint8(v___x_3734_, 13);
if (v_beta_3735_ == 0)
{
lean_dec_ref(v___x_3734_);
v___y_3646_ = v_defEqCtx_x3f_3714_;
v___y_3647_ = v_lctx_3712_;
v___y_3648_ = v_canUnfold_x3f_3716_;
v___y_3649_ = v_synthPendingDepth_3715_;
v___y_3650_ = v_zetaDeltaSet_3711_;
v___y_3651_ = v_cacheInferType_3719_;
v___y_3652_ = v_localInstances_3713_;
v___y_3653_ = v_univApprox_3717_;
v___y_3654_ = v_inTypeClassResolution_3718_;
v___y_3655_ = v_trackZetaDelta_3710_;
v___y_3656_ = v___y_3686_;
v___y_3657_ = v___x_3733_;
goto v___jp_3645_;
}
else
{
uint8_t v_iota_3736_; 
v_iota_3736_ = lean_ctor_get_uint8(v___x_3734_, 12);
if (v_iota_3736_ == 0)
{
lean_dec_ref(v___x_3734_);
v___y_3646_ = v_defEqCtx_x3f_3714_;
v___y_3647_ = v_lctx_3712_;
v___y_3648_ = v_canUnfold_x3f_3716_;
v___y_3649_ = v_synthPendingDepth_3715_;
v___y_3650_ = v_zetaDeltaSet_3711_;
v___y_3651_ = v_cacheInferType_3719_;
v___y_3652_ = v_localInstances_3713_;
v___y_3653_ = v_univApprox_3717_;
v___y_3654_ = v_inTypeClassResolution_3718_;
v___y_3655_ = v_trackZetaDelta_3710_;
v___y_3656_ = v___y_3686_;
v___y_3657_ = v___x_3733_;
goto v___jp_3645_;
}
else
{
uint8_t v_zeta_3737_; 
v_zeta_3737_ = lean_ctor_get_uint8(v___x_3734_, 15);
if (v_zeta_3737_ == 0)
{
lean_dec_ref(v___x_3734_);
v___y_3646_ = v_defEqCtx_x3f_3714_;
v___y_3647_ = v_lctx_3712_;
v___y_3648_ = v_canUnfold_x3f_3716_;
v___y_3649_ = v_synthPendingDepth_3715_;
v___y_3650_ = v_zetaDeltaSet_3711_;
v___y_3651_ = v_cacheInferType_3719_;
v___y_3652_ = v_localInstances_3713_;
v___y_3653_ = v_univApprox_3717_;
v___y_3654_ = v_inTypeClassResolution_3718_;
v___y_3655_ = v_trackZetaDelta_3710_;
v___y_3656_ = v___y_3686_;
v___y_3657_ = v___x_3733_;
goto v___jp_3645_;
}
else
{
uint8_t v_zetaHave_3738_; 
v_zetaHave_3738_ = lean_ctor_get_uint8(v___x_3734_, 18);
if (v_zetaHave_3738_ == 0)
{
lean_dec_ref(v___x_3734_);
v___y_3646_ = v_defEqCtx_x3f_3714_;
v___y_3647_ = v_lctx_3712_;
v___y_3648_ = v_canUnfold_x3f_3716_;
v___y_3649_ = v_synthPendingDepth_3715_;
v___y_3650_ = v_zetaDeltaSet_3711_;
v___y_3651_ = v_cacheInferType_3719_;
v___y_3652_ = v_localInstances_3713_;
v___y_3653_ = v_univApprox_3717_;
v___y_3654_ = v_inTypeClassResolution_3718_;
v___y_3655_ = v_trackZetaDelta_3710_;
v___y_3656_ = v___y_3686_;
v___y_3657_ = v___x_3733_;
goto v___jp_3645_;
}
else
{
uint8_t v_zetaDelta_3739_; 
v_zetaDelta_3739_ = lean_ctor_get_uint8(v___x_3734_, 16);
if (v_zetaDelta_3739_ == 0)
{
lean_dec_ref(v___x_3734_);
v___y_3646_ = v_defEqCtx_x3f_3714_;
v___y_3647_ = v_lctx_3712_;
v___y_3648_ = v_canUnfold_x3f_3716_;
v___y_3649_ = v_synthPendingDepth_3715_;
v___y_3650_ = v_zetaDeltaSet_3711_;
v___y_3651_ = v_cacheInferType_3719_;
v___y_3652_ = v_localInstances_3713_;
v___y_3653_ = v_univApprox_3717_;
v___y_3654_ = v_inTypeClassResolution_3718_;
v___y_3655_ = v_trackZetaDelta_3710_;
v___y_3656_ = v___y_3686_;
v___y_3657_ = v___x_3733_;
goto v___jp_3645_;
}
else
{
uint8_t v_etaStruct_3740_; uint8_t v_proj_3741_; uint8_t v___x_3742_; uint8_t v___x_3743_; 
v_etaStruct_3740_ = lean_ctor_get_uint8(v___x_3734_, 10);
v_proj_3741_ = lean_ctor_get_uint8(v___x_3734_, 14);
lean_dec_ref(v___x_3734_);
v___x_3742_ = 2;
v___x_3743_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3741_, v___x_3742_);
if (v___x_3743_ == 0)
{
v___y_3646_ = v_defEqCtx_x3f_3714_;
v___y_3647_ = v_lctx_3712_;
v___y_3648_ = v_canUnfold_x3f_3716_;
v___y_3649_ = v_synthPendingDepth_3715_;
v___y_3650_ = v_zetaDeltaSet_3711_;
v___y_3651_ = v_cacheInferType_3719_;
v___y_3652_ = v_localInstances_3713_;
v___y_3653_ = v_univApprox_3717_;
v___y_3654_ = v_inTypeClassResolution_3718_;
v___y_3655_ = v_trackZetaDelta_3710_;
v___y_3656_ = v___y_3686_;
v___y_3657_ = v___x_3733_;
goto v___jp_3645_;
}
else
{
uint8_t v___x_3744_; uint8_t v___x_3745_; 
v___x_3744_ = 0;
v___x_3745_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3740_, v___x_3744_);
if (v___x_3745_ == 0)
{
v___y_3646_ = v_defEqCtx_x3f_3714_;
v___y_3647_ = v_lctx_3712_;
v___y_3648_ = v_canUnfold_x3f_3716_;
v___y_3649_ = v_synthPendingDepth_3715_;
v___y_3650_ = v_zetaDeltaSet_3711_;
v___y_3651_ = v_cacheInferType_3719_;
v___y_3652_ = v_localInstances_3713_;
v___y_3653_ = v_univApprox_3717_;
v___y_3654_ = v_inTypeClassResolution_3718_;
v___y_3655_ = v_trackZetaDelta_3710_;
v___y_3656_ = v___y_3686_;
v___y_3657_ = v___x_3733_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3746_; 
lean_dec(v_canUnfold_x3f_3716_);
lean_dec(v_synthPendingDepth_3715_);
lean_dec(v_defEqCtx_x3f_3714_);
lean_dec_ref(v_localInstances_3713_);
lean_dec_ref(v_lctx_3712_);
lean_dec(v_zetaDeltaSet_3711_);
v___x_3746_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3639_, v___x_3733_, v_a_3641_, v___y_3686_, v_a_3643_);
lean_dec(v_a_3643_);
lean_dec_ref(v___y_3686_);
lean_dec(v_a_3641_);
lean_dec_ref(v___x_3733_);
return v___x_3746_;
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
}
}
v_resetjp_3774_:
{
lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3787_ = lean_unsigned_to_nat(0u);
v___x_3788_ = lean_nat_dec_eq(v_maxRecDepth_3762_, v___x_3787_);
if (v___x_3788_ == 0)
{
uint8_t v___x_3789_; 
v___x_3789_ = lean_nat_dec_eq(v_currRecDepth_3761_, v_maxRecDepth_3762_);
if (v___x_3789_ == 0)
{
goto v___jp_3777_;
}
else
{
lean_object* v___x_3790_; 
lean_del_object(v___x_3775_);
lean_dec_ref(v_inheritedTraceOptions_3773_);
lean_dec(v_cancelTk_x3f_3771_);
lean_dec(v_currMacroScope_3769_);
lean_dec(v_quotContext_3768_);
lean_dec(v_maxHeartbeats_3767_);
lean_dec(v_initHeartbeats_3766_);
lean_dec(v_openDecls_3765_);
lean_dec(v_currNamespace_3764_);
lean_dec(v_maxRecDepth_3762_);
lean_dec(v_currRecDepth_3761_);
lean_dec_ref(v_options_3760_);
lean_dec_ref(v_fileMap_3759_);
lean_dec_ref(v_fileName_3758_);
lean_dec(v_a_3643_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
lean_dec_ref(v_e_3639_);
v___x_3790_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3763_);
return v___x_3790_;
}
}
else
{
goto v___jp_3777_;
}
v___jp_3777_:
{
lean_object* v___x_3778_; uint8_t v_transparency_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3778_ = l_Lean_Meta_Context_config(v_a_3640_);
v_transparency_3779_ = lean_ctor_get_uint8(v___x_3778_, 9);
lean_dec_ref(v___x_3778_);
v___x_3780_ = lean_unsigned_to_nat(1u);
v___x_3781_ = lean_nat_add(v_currRecDepth_3761_, v___x_3780_);
lean_dec(v_currRecDepth_3761_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 3, v___x_3781_);
v___x_3783_ = v___x_3775_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_fileName_3758_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_fileMap_3759_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_options_3760_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_maxRecDepth_3762_);
lean_ctor_set(v_reuseFailAlloc_3786_, 5, v_ref_3763_);
lean_ctor_set(v_reuseFailAlloc_3786_, 6, v_currNamespace_3764_);
lean_ctor_set(v_reuseFailAlloc_3786_, 7, v_openDecls_3765_);
lean_ctor_set(v_reuseFailAlloc_3786_, 8, v_initHeartbeats_3766_);
lean_ctor_set(v_reuseFailAlloc_3786_, 9, v_maxHeartbeats_3767_);
lean_ctor_set(v_reuseFailAlloc_3786_, 10, v_quotContext_3768_);
lean_ctor_set(v_reuseFailAlloc_3786_, 11, v_currMacroScope_3769_);
lean_ctor_set(v_reuseFailAlloc_3786_, 12, v_cancelTk_x3f_3771_);
lean_ctor_set(v_reuseFailAlloc_3786_, 13, v_inheritedTraceOptions_3773_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, sizeof(void*)*14, v_diag_3770_);
lean_ctor_set_uint8(v_reuseFailAlloc_3786_, sizeof(void*)*14 + 1, v_suppressElabErrors_3772_);
v___x_3783_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
uint8_t v___x_3784_; uint8_t v___x_3785_; 
v___x_3784_ = 1;
v___x_3785_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3779_, v___x_3784_);
if (v___x_3785_ == 0)
{
v___y_3686_ = v___x_3783_;
v___y_3687_ = v_transparency_3779_;
goto v___jp_3685_;
}
else
{
v___y_3686_ = v___x_3783_;
v___y_3687_ = v___x_3784_;
goto v___jp_3685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = lean_infer_type(v_e_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
return v_res_3798_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3799_){
_start:
{
switch(lean_obj_tag(v_x_3799_))
{
case 0:
{
uint8_t v___x_3800_; 
v___x_3800_ = 1;
return v___x_3800_;
}
case 2:
{
lean_object* v_a_3801_; lean_object* v_a_3802_; uint8_t v___x_3803_; 
v_a_3801_ = lean_ctor_get(v_x_3799_, 0);
v_a_3802_ = lean_ctor_get(v_x_3799_, 1);
v___x_3803_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3801_);
if (v___x_3803_ == 0)
{
return v___x_3803_;
}
else
{
v_x_3799_ = v_a_3802_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3805_; 
v_a_3805_ = lean_ctor_get(v_x_3799_, 1);
v_x_3799_ = v_a_3805_;
goto _start;
}
default: 
{
uint8_t v___x_3807_; 
v___x_3807_ = 0;
return v___x_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3808_){
_start:
{
uint8_t v_res_3809_; lean_object* v_r_3810_; 
v_res_3809_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3808_);
lean_dec(v_x_3808_);
v_r_3810_ = lean_box(v_res_3809_);
return v_r_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v_mctx_3815_; lean_object* v___x_3816_; lean_object* v_fst_3817_; lean_object* v_snd_3818_; lean_object* v___x_3819_; lean_object* v_cache_3820_; lean_object* v_zetaDeltaFVarIds_3821_; lean_object* v_postponed_3822_; lean_object* v_diag_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3832_; 
v___x_3814_ = lean_st_ref_get(v___y_3812_);
v_mctx_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc_ref(v_mctx_3815_);
lean_dec(v___x_3814_);
v___x_3816_ = lean_instantiate_level_mvars(v_mctx_3815_, v_l_3811_);
v_fst_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_fst_3817_);
v_snd_3818_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_snd_3818_);
lean_dec_ref(v___x_3816_);
v___x_3819_ = lean_st_ref_take(v___y_3812_);
v_cache_3820_ = lean_ctor_get(v___x_3819_, 1);
v_zetaDeltaFVarIds_3821_ = lean_ctor_get(v___x_3819_, 2);
v_postponed_3822_ = lean_ctor_get(v___x_3819_, 3);
v_diag_3823_ = lean_ctor_get(v___x_3819_, 4);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v___x_3819_, 0);
lean_dec(v_unused_3833_);
v___x_3825_ = v___x_3819_;
v_isShared_3826_ = v_isSharedCheck_3832_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_diag_3823_);
lean_inc(v_postponed_3822_);
lean_inc(v_zetaDeltaFVarIds_3821_);
lean_inc(v_cache_3820_);
lean_dec(v___x_3819_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3832_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v_fst_3817_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_fst_3817_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_cache_3820_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_zetaDeltaFVarIds_3821_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_postponed_3822_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v_diag_3823_);
v___x_3828_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = lean_st_ref_set(v___y_3812_, v___x_3828_);
v___x_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3830_, 0, v_snd_3818_);
return v___x_3830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3834_, v___y_3835_);
lean_dec(v___y_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3838_, v___y_3840_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3852_, lean_object* v_x_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
switch(lean_obj_tag(v_x_3852_))
{
case 3:
{
lean_object* v_u_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v_u_3863_ = lean_ctor_get(v_x_3852_, 0);
lean_inc(v_u_3863_);
lean_dec_ref(v_x_3852_);
v___x_3864_ = lean_unsigned_to_nat(0u);
v___x_3865_ = lean_nat_dec_eq(v_x_3853_, v___x_3864_);
lean_dec(v_x_3853_);
if (v___x_3865_ == 0)
{
lean_dec(v_u_3863_);
goto v___jp_3859_;
}
else
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3863_, v_a_3855_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3877_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3877_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3877_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
uint8_t v___x_3871_; uint8_t v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3871_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3867_);
lean_dec(v_a_3867_);
v___x_3872_ = l_Bool_toLBool(v___x_3871_);
v___x_3873_ = lean_box(v___x_3872_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3873_);
v___x_3875_ = v___x_3869_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
v_a_3878_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3866_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3866_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3886_; lean_object* v_zero_3887_; uint8_t v_isZero_3888_; 
v_body_3886_ = lean_ctor_get(v_x_3852_, 2);
lean_inc_ref(v_body_3886_);
lean_dec_ref(v_x_3852_);
v_zero_3887_ = lean_unsigned_to_nat(0u);
v_isZero_3888_ = lean_nat_dec_eq(v_x_3853_, v_zero_3887_);
if (v_isZero_3888_ == 1)
{
uint8_t v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_dec_ref(v_body_3886_);
lean_dec(v_x_3853_);
v___x_3889_ = 0;
v___x_3890_ = lean_box(v___x_3889_);
v___x_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
return v___x_3891_;
}
else
{
lean_object* v_one_3892_; lean_object* v_n_3893_; 
v_one_3892_ = lean_unsigned_to_nat(1u);
v_n_3893_ = lean_nat_sub(v_x_3853_, v_one_3892_);
lean_dec(v_x_3853_);
v_x_3852_ = v_body_3886_;
v_x_3853_ = v_n_3893_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3895_; 
v_body_3895_ = lean_ctor_get(v_x_3852_, 3);
lean_inc_ref(v_body_3895_);
lean_dec_ref(v_x_3852_);
v_x_3852_ = v_body_3895_;
goto _start;
}
case 10:
{
lean_object* v_expr_3897_; 
v_expr_3897_ = lean_ctor_get(v_x_3852_, 1);
lean_inc_ref(v_expr_3897_);
lean_dec_ref(v_x_3852_);
v_x_3852_ = v_expr_3897_;
goto _start;
}
default: 
{
lean_dec(v_x_3853_);
lean_dec_ref(v_x_3852_);
goto v___jp_3859_;
}
}
v___jp_3859_:
{
uint8_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3860_ = 2;
v___x_3861_ = lean_box(v___x_3860_);
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3899_, lean_object* v_x_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3899_, v_x_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3907_, lean_object* v_x_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
switch(lean_obj_tag(v_x_3907_))
{
case 4:
{
lean_object* v_declName_3914_; lean_object* v_us_3915_; lean_object* v___x_3916_; 
v_declName_3914_ = lean_ctor_get(v_x_3907_, 0);
lean_inc(v_declName_3914_);
v_us_3915_ = lean_ctor_get(v_x_3907_, 1);
lean_inc(v_us_3915_);
lean_dec_ref(v_x_3907_);
v___x_3916_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3914_, v_us_3915_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref(v___x_3916_);
v___x_3918_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3917_, v_x_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
return v___x_3918_;
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec(v_x_3908_);
v_a_3919_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3916_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3916_);
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
case 1:
{
lean_object* v_fvarId_3927_; lean_object* v___x_3928_; 
v_fvarId_3927_ = lean_ctor_get(v_x_3907_, 0);
lean_inc(v_fvarId_3927_);
lean_dec_ref(v_x_3907_);
v___x_3928_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3927_, v_a_3909_, v_a_3911_, v_a_3912_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref(v___x_3928_);
v___x_3930_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3929_, v_x_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
return v___x_3930_;
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec(v_x_3908_);
v_a_3931_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3928_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3928_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3939_; lean_object* v___x_3940_; 
v_mvarId_3939_ = lean_ctor_get(v_x_3907_, 0);
lean_inc(v_mvarId_3939_);
lean_dec_ref(v_x_3907_);
v___x_3940_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3939_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3942_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref(v___x_3940_);
v___x_3942_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3941_, v_x_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
return v___x_3942_;
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec(v_x_3908_);
v_a_3943_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3940_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3940_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
case 5:
{
lean_object* v_fn_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_fn_3951_ = lean_ctor_get(v_x_3907_, 0);
lean_inc_ref(v_fn_3951_);
lean_dec_ref(v_x_3907_);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_nat_add(v_x_3908_, v___x_3952_);
lean_dec(v_x_3908_);
v_x_3907_ = v_fn_3951_;
v_x_3908_ = v___x_3953_;
goto _start;
}
case 10:
{
lean_object* v_expr_3955_; 
v_expr_3955_ = lean_ctor_get(v_x_3907_, 1);
lean_inc_ref(v_expr_3955_);
lean_dec_ref(v_x_3907_);
v_x_3907_ = v_expr_3955_;
goto _start;
}
case 8:
{
lean_object* v_body_3957_; 
v_body_3957_ = lean_ctor_get(v_x_3907_, 3);
lean_inc_ref(v_body_3957_);
lean_dec_ref(v_x_3907_);
v_x_3907_ = v_body_3957_;
goto _start;
}
case 6:
{
lean_object* v_body_3959_; lean_object* v_zero_3960_; uint8_t v_isZero_3961_; 
v_body_3959_ = lean_ctor_get(v_x_3907_, 2);
lean_inc_ref(v_body_3959_);
lean_dec_ref(v_x_3907_);
v_zero_3960_ = lean_unsigned_to_nat(0u);
v_isZero_3961_ = lean_nat_dec_eq(v_x_3908_, v_zero_3960_);
if (v_isZero_3961_ == 1)
{
uint8_t v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec_ref(v_body_3959_);
lean_dec(v_x_3908_);
v___x_3962_ = 0;
v___x_3963_ = lean_box(v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
return v___x_3964_;
}
else
{
lean_object* v_one_3965_; lean_object* v_n_3966_; 
v_one_3965_ = lean_unsigned_to_nat(1u);
v_n_3966_ = lean_nat_sub(v_x_3908_, v_one_3965_);
lean_dec(v_x_3908_);
v_x_3907_ = v_body_3959_;
v_x_3908_ = v_n_3966_;
goto _start;
}
}
default: 
{
uint8_t v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_dec(v_x_3908_);
lean_dec_ref(v_x_3907_);
v___x_3968_ = 2;
v___x_3969_ = lean_box(v___x_3968_);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3971_, lean_object* v_x_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3971_, v_x_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
switch(lean_obj_tag(v_x_3979_))
{
case 0:
{
uint8_t v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
lean_dec_ref(v_x_3979_);
v___x_3985_ = 2;
v___x_3986_ = lean_box(v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
return v___x_3987_;
}
case 1:
{
lean_object* v_fvarId_3988_; lean_object* v___x_3989_; 
v_fvarId_3988_ = lean_ctor_get(v_x_3979_, 0);
lean_inc(v_fvarId_3988_);
lean_dec_ref(v_x_3979_);
v___x_3989_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3988_, v_a_3980_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref(v___x_3989_);
v___x_3991_ = lean_unsigned_to_nat(0u);
v___x_3992_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3990_, v___x_3991_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_3992_;
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_a_3993_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3989_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3989_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4001_; lean_object* v___x_4002_; 
v_mvarId_4001_ = lean_ctor_get(v_x_3979_, 0);
lean_inc(v_mvarId_4001_);
lean_dec_ref(v_x_3979_);
v___x_4002_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4001_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref(v___x_4002_);
v___x_4004_ = lean_unsigned_to_nat(0u);
v___x_4005_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4003_, v___x_4004_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_4005_;
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4002_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4002_);
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
case 4:
{
lean_object* v_declName_4014_; lean_object* v_us_4015_; lean_object* v___x_4016_; 
v_declName_4014_ = lean_ctor_get(v_x_3979_, 0);
lean_inc(v_declName_4014_);
v_us_4015_ = lean_ctor_get(v_x_3979_, 1);
lean_inc(v_us_4015_);
lean_dec_ref(v_x_3979_);
v___x_4016_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4014_, v_us_4015_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref(v___x_4016_);
v___x_4018_ = lean_unsigned_to_nat(0u);
v___x_4019_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_4017_, v___x_4018_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_4019_;
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
v_a_4020_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4016_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4016_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
case 5:
{
lean_object* v_fn_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_fn_4028_ = lean_ctor_get(v_x_3979_, 0);
lean_inc_ref(v_fn_4028_);
lean_dec_ref(v_x_3979_);
v___x_4029_ = lean_unsigned_to_nat(1u);
v___x_4030_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_4028_, v___x_4029_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_4030_;
}
case 7:
{
lean_object* v_body_4031_; 
v_body_4031_ = lean_ctor_get(v_x_3979_, 2);
lean_inc_ref(v_body_4031_);
lean_dec_ref(v_x_3979_);
v_x_3979_ = v_body_4031_;
goto _start;
}
case 8:
{
lean_object* v_body_4033_; 
v_body_4033_ = lean_ctor_get(v_x_3979_, 3);
lean_inc_ref(v_body_4033_);
lean_dec_ref(v_x_3979_);
v_x_3979_ = v_body_4033_;
goto _start;
}
case 10:
{
lean_object* v_expr_4035_; 
v_expr_4035_ = lean_ctor_get(v_x_3979_, 1);
lean_inc_ref(v_expr_4035_);
lean_dec_ref(v_x_3979_);
v_x_3979_ = v_expr_4035_;
goto _start;
}
case 11:
{
uint8_t v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec_ref(v_x_3979_);
v___x_4037_ = 2;
v___x_4038_ = lean_box(v___x_4037_);
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
return v___x_4039_;
}
default: 
{
uint8_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec_ref(v_x_3979_);
v___x_4040_ = 0;
v___x_4041_ = lean_box(v___x_4040_);
v___x_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
return v___x_4042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_Meta_isPropQuick(v_x_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v___x_4056_; 
lean_inc_ref(v_e_4050_);
v___x_4056_ = l_Lean_Meta_isPropQuick(v_e_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4113_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4059_ = v___x_4056_;
v_isShared_4060_ = v_isSharedCheck_4113_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4056_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4113_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
uint8_t v___x_4061_; 
v___x_4061_ = lean_unbox(v_a_4057_);
lean_dec(v_a_4057_);
switch(v___x_4061_)
{
case 0:
{
uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
lean_dec_ref(v_e_4050_);
v___x_4062_ = 0;
v___x_4063_ = lean_box(v___x_4062_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v___x_4063_);
v___x_4065_ = v___x_4059_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
case 1:
{
uint8_t v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_dec_ref(v_e_4050_);
v___x_4067_ = 1;
v___x_4068_ = lean_box(v___x_4067_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v___x_4068_);
v___x_4070_ = v___x_4059_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
default: 
{
lean_object* v___x_4072_; 
lean_del_object(v___x_4059_);
lean_inc(v_a_4054_);
lean_inc_ref(v_a_4053_);
lean_inc(v_a_4052_);
lean_inc_ref(v_a_4051_);
v___x_4072_ = lean_infer_type(v_e_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4074_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref(v___x_4072_);
v___x_4074_ = l_Lean_Meta_whnfD(v_a_4073_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4096_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4077_ = v___x_4074_;
v_isShared_4078_ = v_isSharedCheck_4096_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4096_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
if (lean_obj_tag(v_a_4075_) == 3)
{
lean_object* v_u_4079_; lean_object* v___x_4080_; lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4090_; 
lean_del_object(v___x_4077_);
v_u_4079_ = lean_ctor_get(v_a_4075_, 0);
lean_inc(v_u_4079_);
lean_dec_ref(v_a_4075_);
v___x_4080_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_4079_, v_a_4052_);
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4083_ = v___x_4080_;
v_isShared_4084_ = v_isSharedCheck_4090_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4090_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4085_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_4081_);
lean_dec(v_a_4081_);
v___x_4086_ = lean_box(v___x_4085_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 0, v___x_4086_);
v___x_4088_ = v___x_4083_;
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
}
else
{
uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
lean_dec(v_a_4075_);
v___x_4091_ = 0;
v___x_4092_ = lean_box(v___x_4091_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 0, v___x_4092_);
v___x_4094_ = v___x_4077_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
v_a_4097_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4074_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4074_);
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
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
v_a_4105_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4072_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4072_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec_ref(v_e_4050_);
v_a_4114_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4056_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4056_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Meta_isProp(v_e_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_4129_){
_start:
{
switch(lean_obj_tag(v_x_4129_))
{
case 0:
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_unsigned_to_nat(0u);
return v___x_4130_;
}
case 1:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_unsigned_to_nat(1u);
return v___x_4131_;
}
case 2:
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_unsigned_to_nat(2u);
return v___x_4132_;
}
default: 
{
lean_object* v___x_4133_; 
v___x_4133_ = lean_unsigned_to_nat(3u);
return v___x_4133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_4134_);
lean_dec(v_x_4134_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_4136_, lean_object* v_k_4137_){
_start:
{
if (lean_obj_tag(v_t_4136_) == 3)
{
lean_object* v_idx_4138_; lean_object* v___x_4139_; 
v_idx_4138_ = lean_ctor_get(v_t_4136_, 0);
lean_inc(v_idx_4138_);
lean_dec_ref(v_t_4136_);
v___x_4139_ = lean_apply_1(v_k_4137_, v_idx_4138_);
return v___x_4139_;
}
else
{
lean_dec(v_t_4136_);
return v_k_4137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_4140_, lean_object* v_ctorIdx_4141_, lean_object* v_t_4142_, lean_object* v_h_4143_, lean_object* v_k_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4142_, v_k_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_4146_, lean_object* v_ctorIdx_4147_, lean_object* v_t_4148_, lean_object* v_h_4149_, lean_object* v_k_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_4146_, v_ctorIdx_4147_, v_t_4148_, v_h_4149_, v_k_4150_);
lean_dec(v_ctorIdx_4147_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_4152_, lean_object* v_false_4153_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4152_, v_false_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_4155_, lean_object* v_t_4156_, lean_object* v_h_4157_, lean_object* v_false_4158_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4156_, v_false_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_4160_, lean_object* v_true_4161_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4160_, v_true_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_4163_, lean_object* v_t_4164_, lean_object* v_h_4165_, lean_object* v_true_4166_){
_start:
{
lean_object* v___x_4167_; 
v___x_4167_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4164_, v_true_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_4168_, lean_object* v_undef_4169_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4168_, v_undef_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_4171_, lean_object* v_t_4172_, lean_object* v_h_4173_, lean_object* v_undef_4174_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4172_, v_undef_4174_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_4176_, lean_object* v_bvar_4177_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4176_, v_bvar_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_4179_, lean_object* v_t_4180_, lean_object* v_h_4181_, lean_object* v_bvar_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_4180_, v_bvar_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_4184_){
_start:
{
switch(v_x_4184_)
{
case 0:
{
lean_object* v___x_4185_; 
v___x_4185_ = lean_box(0);
return v___x_4185_;
}
case 1:
{
lean_object* v___x_4186_; 
v___x_4186_ = lean_box(1);
return v___x_4186_;
}
default: 
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_box(2);
return v___x_4187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_4188_){
_start:
{
uint8_t v_x_25__boxed_4189_; lean_object* v_res_4190_; 
v_x_25__boxed_4189_ = lean_unbox(v_x_4188_);
v_res_4190_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_4189_);
return v_res_4190_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_4191_){
_start:
{
switch(lean_obj_tag(v_x_4191_))
{
case 0:
{
uint8_t v___x_4192_; 
v___x_4192_ = 0;
return v___x_4192_;
}
case 1:
{
uint8_t v___x_4193_; 
v___x_4193_ = 1;
return v___x_4193_;
}
default: 
{
uint8_t v___x_4194_; 
v___x_4194_ = 2;
return v___x_4194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_4195_){
_start:
{
uint8_t v_res_4196_; lean_object* v_r_4197_; 
v_res_4196_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_4195_);
lean_dec(v_x_4195_);
v_r_4197_ = lean_box(v_res_4196_);
return v_r_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4199_){
_start:
{
switch(lean_obj_tag(v_e_4199_))
{
case 3:
{
lean_object* v_u_4200_; uint8_t v___x_4201_; 
v_u_4200_ = lean_ctor_get(v_e_4199_, 0);
v___x_4201_ = l_Lean_Level_isNeverZero(v_u_4200_);
if (v___x_4201_ == 0)
{
uint8_t v___x_4202_; 
v___x_4202_ = l_Lean_Level_isZero(v_u_4200_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_box(2);
return v___x_4203_;
}
else
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_box(1);
return v___x_4204_;
}
}
else
{
lean_object* v___x_4205_; 
v___x_4205_ = lean_box(0);
return v___x_4205_;
}
}
case 5:
{
lean_object* v_fn_4206_; 
v_fn_4206_ = lean_ctor_get(v_e_4199_, 0);
if (lean_obj_tag(v_fn_4206_) == 4)
{
lean_object* v_declName_4207_; 
v_declName_4207_ = lean_ctor_get(v_fn_4206_, 0);
if (lean_obj_tag(v_declName_4207_) == 1)
{
lean_object* v_pre_4208_; 
v_pre_4208_ = lean_ctor_get(v_declName_4207_, 0);
if (lean_obj_tag(v_pre_4208_) == 0)
{
lean_object* v_arg_4209_; lean_object* v_str_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v_arg_4209_ = lean_ctor_get(v_e_4199_, 1);
v_str_4210_ = lean_ctor_get(v_declName_4207_, 1);
v___x_4211_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4212_ = lean_string_dec_eq(v_str_4210_, v___x_4211_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4213_; 
v___x_4213_ = lean_box(2);
return v___x_4213_;
}
else
{
v_e_4199_ = v_arg_4209_;
goto _start;
}
}
else
{
lean_object* v___x_4215_; 
v___x_4215_ = lean_box(2);
return v___x_4215_;
}
}
else
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_box(2);
return v___x_4216_;
}
}
else
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_box(2);
return v___x_4217_;
}
}
default: 
{
lean_object* v___x_4218_; 
v___x_4218_ = lean_box(2);
return v___x_4218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4219_);
lean_dec_ref(v_e_4219_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4221_, lean_object* v_binderType_4222_){
_start:
{
if (lean_obj_tag(v_r_4221_) == 3)
{
lean_object* v_idx_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4235_; 
v_idx_4223_ = lean_ctor_get(v_r_4221_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_r_4221_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4225_ = v_r_4221_;
v_isShared_4226_ = v_isSharedCheck_4235_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_idx_4223_);
lean_dec(v_r_4221_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4235_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v_zero_4227_; uint8_t v_isZero_4228_; 
v_zero_4227_ = lean_unsigned_to_nat(0u);
v_isZero_4228_ = lean_nat_dec_eq(v_idx_4223_, v_zero_4227_);
if (v_isZero_4228_ == 1)
{
lean_object* v___x_4229_; 
lean_del_object(v___x_4225_);
lean_dec(v_idx_4223_);
v___x_4229_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4222_);
return v___x_4229_;
}
else
{
lean_object* v_one_4230_; lean_object* v_n_4231_; lean_object* v___x_4233_; 
v_one_4230_ = lean_unsigned_to_nat(1u);
v_n_4231_ = lean_nat_sub(v_idx_4223_, v_one_4230_);
lean_dec(v_idx_4223_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v_n_4231_);
v___x_4233_ = v___x_4225_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_n_4231_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
else
{
return v_r_4221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4236_, lean_object* v_binderType_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4236_, v_binderType_4237_);
lean_dec_ref(v_binderType_4237_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4239_, lean_object* v_x_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v_type_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; 
switch(lean_obj_tag(v_x_4239_))
{
case 7:
{
lean_object* v_binderType_4274_; lean_object* v_body_4275_; lean_object* v_zero_4276_; uint8_t v_isZero_4277_; 
v_binderType_4274_ = lean_ctor_get(v_x_4239_, 1);
v_body_4275_ = lean_ctor_get(v_x_4239_, 2);
v_zero_4276_ = lean_unsigned_to_nat(0u);
v_isZero_4277_ = lean_nat_dec_eq(v_x_4240_, v_zero_4276_);
if (v_isZero_4277_ == 1)
{
v_type_4247_ = v_x_4239_;
v___y_4248_ = v_a_4241_;
v___y_4249_ = v_a_4242_;
v___y_4250_ = v_a_4243_;
v___y_4251_ = v_a_4244_;
goto v___jp_4246_;
}
else
{
lean_object* v_one_4278_; lean_object* v_n_4279_; lean_object* v___x_4280_; 
lean_inc_ref(v_body_4275_);
lean_inc_ref(v_binderType_4274_);
lean_dec_ref(v_x_4239_);
v_one_4278_ = lean_unsigned_to_nat(1u);
v_n_4279_ = lean_nat_sub(v_x_4240_, v_one_4278_);
v___x_4280_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4275_, v_n_4279_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
lean_dec(v_n_4279_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4289_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4283_ = v___x_4280_;
v_isShared_4284_ = v_isSharedCheck_4289_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4289_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4285_; lean_object* v___x_4287_; 
v___x_4285_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4281_, v_binderType_4274_);
lean_dec_ref(v_binderType_4274_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 0, v___x_4285_);
v___x_4287_ = v___x_4283_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4285_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
else
{
lean_dec_ref(v_binderType_4274_);
return v___x_4280_;
}
}
}
case 8:
{
lean_object* v_type_4290_; lean_object* v_body_4291_; lean_object* v___x_4292_; 
v_type_4290_ = lean_ctor_get(v_x_4239_, 1);
lean_inc_ref(v_type_4290_);
v_body_4291_ = lean_ctor_get(v_x_4239_, 3);
lean_inc_ref(v_body_4291_);
lean_dec_ref(v_x_4239_);
v___x_4292_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4291_, v_x_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4301_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4301_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4301_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4297_; lean_object* v___x_4299_; 
v___x_4297_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4293_, v_type_4290_);
lean_dec_ref(v_type_4290_);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4297_);
v___x_4299_ = v___x_4295_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
else
{
lean_dec_ref(v_type_4290_);
return v___x_4292_;
}
}
case 10:
{
lean_object* v_expr_4302_; 
v_expr_4302_ = lean_ctor_get(v_x_4239_, 1);
lean_inc_ref(v_expr_4302_);
lean_dec_ref(v_x_4239_);
v_x_4239_ = v_expr_4302_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v_deBruijnIndex_4304_ = lean_ctor_get(v_x_4239_, 0);
lean_inc(v_deBruijnIndex_4304_);
lean_dec_ref(v_x_4239_);
v___x_4305_ = lean_unsigned_to_nat(0u);
v___x_4306_ = lean_nat_dec_eq(v_x_4240_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec(v_deBruijnIndex_4304_);
goto v___jp_4271_;
}
else
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4307_, 0, v_deBruijnIndex_4304_);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
return v___x_4308_;
}
}
default: 
{
lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4309_ = lean_unsigned_to_nat(0u);
v___x_4310_ = lean_nat_dec_eq(v_x_4240_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_dec_ref(v_x_4239_);
goto v___jp_4271_;
}
else
{
v_type_4247_ = v_x_4239_;
v___y_4248_ = v_a_4241_;
v___y_4249_ = v_a_4242_;
v___y_4250_ = v_a_4243_;
v___y_4251_ = v_a_4244_;
goto v___jp_4246_;
}
}
}
v___jp_4246_:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_isPropQuick(v_type_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4262_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4255_ = v___x_4252_;
v_isShared_4256_ = v_isSharedCheck_4262_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4262_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
uint8_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4260_; 
v___x_4257_ = lean_unbox(v_a_4253_);
lean_dec(v_a_4253_);
v___x_4258_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4257_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4258_);
v___x_4260_ = v___x_4255_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
v_a_4263_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4252_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4252_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
v___jp_4271_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = lean_box(2);
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
return v___x_4273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4311_, lean_object* v_x_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4311_, v_x_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_x_4312_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4319_, lean_object* v_n_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4319_, v_n_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4336_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4329_ = v___x_4326_;
v_isShared_4330_ = v_isSharedCheck_4336_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4326_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4336_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
uint8_t v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4334_; 
v___x_4331_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4327_);
lean_dec(v_a_4327_);
v___x_4332_ = lean_box(v___x_4331_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4332_);
v___x_4334_ = v___x_4329_;
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
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_a_4337_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4326_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4326_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4345_, lean_object* v_n_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4345_, v_n_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_n_4346_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4353_, lean_object* v_x_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
switch(lean_obj_tag(v_x_4353_))
{
case 4:
{
lean_object* v_declName_4360_; lean_object* v_us_4361_; lean_object* v___x_4362_; 
v_declName_4360_ = lean_ctor_get(v_x_4353_, 0);
lean_inc(v_declName_4360_);
v_us_4361_ = lean_ctor_get(v_x_4353_, 1);
lean_inc(v_us_4361_);
lean_dec_ref(v_x_4353_);
v___x_4362_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4360_, v_us_4361_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4364_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref(v___x_4362_);
v___x_4364_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4363_, v_x_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
lean_dec(v_x_4354_);
return v___x_4364_;
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v_x_4354_);
v_a_4365_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4362_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4362_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4373_; lean_object* v___x_4374_; 
v_fvarId_4373_ = lean_ctor_get(v_x_4353_, 0);
lean_inc(v_fvarId_4373_);
lean_dec_ref(v_x_4353_);
v___x_4374_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4373_, v_a_4355_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4376_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref(v___x_4374_);
v___x_4376_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4375_, v_x_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
lean_dec(v_x_4354_);
return v___x_4376_;
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_x_4354_);
v_a_4377_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4374_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4374_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4385_; lean_object* v___x_4386_; 
v_mvarId_4385_ = lean_ctor_get(v_x_4353_, 0);
lean_inc(v_mvarId_4385_);
lean_dec_ref(v_x_4353_);
v___x_4386_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4385_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4388_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref(v___x_4386_);
v___x_4388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4387_, v_x_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
lean_dec(v_x_4354_);
return v___x_4388_;
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_x_4354_);
v_a_4389_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4386_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4386_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
case 5:
{
lean_object* v_fn_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v_fn_4397_ = lean_ctor_get(v_x_4353_, 0);
lean_inc_ref(v_fn_4397_);
lean_dec_ref(v_x_4353_);
v___x_4398_ = lean_unsigned_to_nat(1u);
v___x_4399_ = lean_nat_add(v_x_4354_, v___x_4398_);
lean_dec(v_x_4354_);
v_x_4353_ = v_fn_4397_;
v_x_4354_ = v___x_4399_;
goto _start;
}
case 10:
{
lean_object* v_expr_4401_; 
v_expr_4401_ = lean_ctor_get(v_x_4353_, 1);
lean_inc_ref(v_expr_4401_);
lean_dec_ref(v_x_4353_);
v_x_4353_ = v_expr_4401_;
goto _start;
}
case 8:
{
lean_object* v_body_4403_; 
v_body_4403_ = lean_ctor_get(v_x_4353_, 3);
lean_inc_ref(v_body_4403_);
lean_dec_ref(v_x_4353_);
v_x_4353_ = v_body_4403_;
goto _start;
}
case 6:
{
lean_object* v_body_4405_; lean_object* v_zero_4406_; uint8_t v_isZero_4407_; 
v_body_4405_ = lean_ctor_get(v_x_4353_, 2);
lean_inc_ref(v_body_4405_);
lean_dec_ref(v_x_4353_);
v_zero_4406_ = lean_unsigned_to_nat(0u);
v_isZero_4407_ = lean_nat_dec_eq(v_x_4354_, v_zero_4406_);
if (v_isZero_4407_ == 1)
{
lean_object* v___x_4408_; 
lean_dec(v_x_4354_);
v___x_4408_ = l_Lean_Meta_isProofQuick(v_body_4405_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
return v___x_4408_;
}
else
{
lean_object* v_one_4409_; lean_object* v_n_4410_; 
v_one_4409_ = lean_unsigned_to_nat(1u);
v_n_4410_ = lean_nat_sub(v_x_4354_, v_one_4409_);
lean_dec(v_x_4354_);
v_x_4353_ = v_body_4405_;
v_x_4354_ = v_n_4410_;
goto _start;
}
}
default: 
{
uint8_t v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
lean_dec(v_x_4354_);
lean_dec_ref(v_x_4353_);
v___x_4412_ = 2;
v___x_4413_ = lean_box(v___x_4412_);
v___x_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
return v___x_4414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
switch(lean_obj_tag(v_x_4415_))
{
case 0:
{
uint8_t v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_dec_ref(v_x_4415_);
v___x_4421_ = 2;
v___x_4422_ = lean_box(v___x_4421_);
v___x_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
return v___x_4423_;
}
case 1:
{
lean_object* v_fvarId_4424_; lean_object* v___x_4425_; 
v_fvarId_4424_ = lean_ctor_get(v_x_4415_, 0);
lean_inc(v_fvarId_4424_);
lean_dec_ref(v_x_4415_);
v___x_4425_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4424_, v_a_4416_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref(v___x_4425_);
v___x_4427_ = lean_unsigned_to_nat(0u);
v___x_4428_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4426_, v___x_4427_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
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
case 2:
{
lean_object* v_mvarId_4437_; lean_object* v___x_4438_; 
v_mvarId_4437_ = lean_ctor_get(v_x_4415_, 0);
lean_inc(v_mvarId_4437_);
lean_dec_ref(v_x_4415_);
v___x_4438_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4437_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_a_4439_);
lean_dec_ref(v___x_4438_);
v___x_4440_ = lean_unsigned_to_nat(0u);
v___x_4441_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4439_, v___x_4440_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
return v___x_4441_;
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
v_a_4442_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4438_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4438_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
case 4:
{
lean_object* v_declName_4450_; lean_object* v_us_4451_; lean_object* v___x_4452_; 
v_declName_4450_ = lean_ctor_get(v_x_4415_, 0);
lean_inc(v_declName_4450_);
v_us_4451_ = lean_ctor_get(v_x_4415_, 1);
lean_inc(v_us_4451_);
lean_dec_ref(v_x_4415_);
v___x_4452_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4450_, v_us_4451_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref(v___x_4452_);
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
lean_dec_ref(v_x_4415_);
v___x_4465_ = lean_unsigned_to_nat(1u);
v___x_4466_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4464_, v___x_4465_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_);
return v___x_4466_;
}
case 6:
{
lean_object* v_body_4467_; 
v_body_4467_ = lean_ctor_get(v_x_4415_, 2);
lean_inc_ref(v_body_4467_);
lean_dec_ref(v_x_4415_);
v_x_4415_ = v_body_4467_;
goto _start;
}
case 8:
{
lean_object* v_body_4469_; 
v_body_4469_ = lean_ctor_get(v_x_4415_, 3);
lean_inc_ref(v_body_4469_);
lean_dec_ref(v_x_4415_);
v_x_4415_ = v_body_4469_;
goto _start;
}
case 10:
{
lean_object* v_expr_4471_; 
v_expr_4471_ = lean_ctor_get(v_x_4415_, 1);
lean_inc_ref(v_expr_4471_);
lean_dec_ref(v_x_4415_);
v_x_4415_ = v_expr_4471_;
goto _start;
}
case 11:
{
uint8_t v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec_ref(v_x_4415_);
v___x_4473_ = 2;
v___x_4474_ = lean_box(v___x_4473_);
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
return v___x_4475_;
}
default: 
{
uint8_t v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
lean_dec_ref(v_x_4415_);
v___x_4476_ = 0;
v___x_4477_ = lean_box(v___x_4476_);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
return v___x_4478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_Meta_isProofQuick(v_x_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4486_, lean_object* v_x_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4486_, v_x_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v___x_4500_; 
lean_inc_ref(v_e_4494_);
v___x_4500_ = l_Lean_Meta_isProofQuick(v_e_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4527_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4503_ = v___x_4500_;
v_isShared_4504_ = v_isSharedCheck_4527_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4500_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4527_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
uint8_t v___x_4505_; 
v___x_4505_ = lean_unbox(v_a_4501_);
lean_dec(v_a_4501_);
switch(v___x_4505_)
{
case 0:
{
uint8_t v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4509_; 
lean_dec_ref(v_e_4494_);
v___x_4506_ = 0;
v___x_4507_ = lean_box(v___x_4506_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4507_);
v___x_4509_ = v___x_4503_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
case 1:
{
uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
lean_dec_ref(v_e_4494_);
v___x_4511_ = 1;
v___x_4512_ = lean_box(v___x_4511_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4512_);
v___x_4514_ = v___x_4503_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
default: 
{
lean_object* v___x_4516_; 
lean_del_object(v___x_4503_);
lean_inc(v_a_4498_);
lean_inc_ref(v_a_4497_);
lean_inc(v_a_4496_);
lean_inc_ref(v_a_4495_);
v___x_4516_ = lean_infer_type(v_e_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4518_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_a_4517_);
lean_dec_ref(v___x_4516_);
v___x_4518_ = l_Lean_Meta_isProp(v_a_4517_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
return v___x_4518_;
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
v_a_4519_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4516_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4516_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
lean_dec_ref(v_e_4494_);
v_a_4528_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4500_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4500_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_Meta_isProof(v_e_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4543_, lean_object* v_x_4544_){
_start:
{
switch(lean_obj_tag(v_x_4543_))
{
case 3:
{
lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4550_ = lean_unsigned_to_nat(0u);
v___x_4551_ = lean_nat_dec_eq(v_x_4544_, v___x_4550_);
lean_dec(v_x_4544_);
if (v___x_4551_ == 0)
{
goto v___jp_4546_;
}
else
{
uint8_t v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = 1;
v___x_4553_ = lean_box(v___x_4552_);
v___x_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
return v___x_4554_;
}
}
case 7:
{
lean_object* v_body_4555_; lean_object* v_zero_4556_; uint8_t v_isZero_4557_; 
v_body_4555_ = lean_ctor_get(v_x_4543_, 2);
v_zero_4556_ = lean_unsigned_to_nat(0u);
v_isZero_4557_ = lean_nat_dec_eq(v_x_4544_, v_zero_4556_);
if (v_isZero_4557_ == 1)
{
uint8_t v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_dec(v_x_4544_);
v___x_4558_ = 0;
v___x_4559_ = lean_box(v___x_4558_);
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
return v___x_4560_;
}
else
{
lean_object* v_one_4561_; lean_object* v_n_4562_; 
v_one_4561_ = lean_unsigned_to_nat(1u);
v_n_4562_ = lean_nat_sub(v_x_4544_, v_one_4561_);
lean_dec(v_x_4544_);
v_x_4543_ = v_body_4555_;
v_x_4544_ = v_n_4562_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4564_; 
v_body_4564_ = lean_ctor_get(v_x_4543_, 3);
v_x_4543_ = v_body_4564_;
goto _start;
}
case 10:
{
lean_object* v_expr_4566_; 
v_expr_4566_ = lean_ctor_get(v_x_4543_, 1);
v_x_4543_ = v_expr_4566_;
goto _start;
}
default: 
{
lean_dec(v_x_4544_);
goto v___jp_4546_;
}
}
v___jp_4546_:
{
uint8_t v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = 2;
v___x_4548_ = lean_box(v___x_4547_);
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
return v___x_4549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4568_, lean_object* v_x_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4568_, v_x_4569_);
lean_dec_ref(v_x_4568_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4572_, lean_object* v_x_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4572_, v_x_4573_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4580_, lean_object* v_x_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4580_, v_x_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
lean_dec_ref(v_x_4580_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4588_, lean_object* v_x_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
switch(lean_obj_tag(v_x_4588_))
{
case 4:
{
lean_object* v_declName_4595_; lean_object* v_us_4596_; lean_object* v___x_4597_; 
v_declName_4595_ = lean_ctor_get(v_x_4588_, 0);
lean_inc(v_declName_4595_);
v_us_4596_ = lean_ctor_get(v_x_4588_, 1);
lean_inc(v_us_4596_);
lean_dec_ref(v_x_4588_);
v___x_4597_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4595_, v_us_4596_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4599_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref(v___x_4597_);
v___x_4599_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4598_, v_x_4589_);
lean_dec(v_a_4598_);
return v___x_4599_;
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
lean_dec(v_x_4589_);
v_a_4600_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4597_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4597_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4608_; lean_object* v___x_4609_; 
v_fvarId_4608_ = lean_ctor_get(v_x_4588_, 0);
lean_inc(v_fvarId_4608_);
lean_dec_ref(v_x_4588_);
v___x_4609_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4608_, v_a_4590_, v_a_4592_, v_a_4593_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4611_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref(v___x_4609_);
v___x_4611_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4610_, v_x_4589_);
lean_dec(v_a_4610_);
return v___x_4611_;
}
else
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
lean_dec(v_x_4589_);
v_a_4612_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4609_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4609_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4620_; lean_object* v___x_4621_; 
v_mvarId_4620_ = lean_ctor_get(v_x_4588_, 0);
lean_inc(v_mvarId_4620_);
lean_dec_ref(v_x_4588_);
v___x_4621_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4620_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4623_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_a_4622_);
lean_dec_ref(v___x_4621_);
v___x_4623_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4622_, v_x_4589_);
lean_dec(v_a_4622_);
return v___x_4623_;
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v_x_4589_);
v_a_4624_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4621_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4621_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
case 5:
{
lean_object* v_fn_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v_fn_4632_ = lean_ctor_get(v_x_4588_, 0);
lean_inc_ref(v_fn_4632_);
lean_dec_ref(v_x_4588_);
v___x_4633_ = lean_unsigned_to_nat(1u);
v___x_4634_ = lean_nat_add(v_x_4589_, v___x_4633_);
lean_dec(v_x_4589_);
v_x_4588_ = v_fn_4632_;
v_x_4589_ = v___x_4634_;
goto _start;
}
case 10:
{
lean_object* v_expr_4636_; 
v_expr_4636_ = lean_ctor_get(v_x_4588_, 1);
lean_inc_ref(v_expr_4636_);
lean_dec_ref(v_x_4588_);
v_x_4588_ = v_expr_4636_;
goto _start;
}
case 8:
{
lean_object* v_body_4638_; 
v_body_4638_ = lean_ctor_get(v_x_4588_, 3);
lean_inc_ref(v_body_4638_);
lean_dec_ref(v_x_4588_);
v_x_4588_ = v_body_4638_;
goto _start;
}
case 6:
{
lean_object* v_body_4640_; lean_object* v_zero_4641_; uint8_t v_isZero_4642_; 
v_body_4640_ = lean_ctor_get(v_x_4588_, 2);
lean_inc_ref(v_body_4640_);
lean_dec_ref(v_x_4588_);
v_zero_4641_ = lean_unsigned_to_nat(0u);
v_isZero_4642_ = lean_nat_dec_eq(v_x_4589_, v_zero_4641_);
if (v_isZero_4642_ == 1)
{
uint8_t v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
lean_dec_ref(v_body_4640_);
lean_dec(v_x_4589_);
v___x_4643_ = 0;
v___x_4644_ = lean_box(v___x_4643_);
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
else
{
lean_object* v_one_4646_; lean_object* v_n_4647_; 
v_one_4646_ = lean_unsigned_to_nat(1u);
v_n_4647_ = lean_nat_sub(v_x_4589_, v_one_4646_);
lean_dec(v_x_4589_);
v_x_4588_ = v_body_4640_;
v_x_4589_ = v_n_4647_;
goto _start;
}
}
default: 
{
uint8_t v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
lean_dec(v_x_4589_);
lean_dec_ref(v_x_4588_);
v___x_4649_ = 2;
v___x_4650_ = lean_box(v___x_4649_);
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
return v___x_4651_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4652_, lean_object* v_x_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4652_, v_x_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
switch(lean_obj_tag(v_x_4660_))
{
case 1:
{
lean_object* v_fvarId_4666_; lean_object* v___x_4667_; 
v_fvarId_4666_ = lean_ctor_get(v_x_4660_, 0);
lean_inc(v_fvarId_4666_);
lean_dec_ref(v_x_4660_);
v___x_4667_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4666_, v_a_4661_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref(v___x_4667_);
v___x_4669_ = lean_unsigned_to_nat(0u);
v___x_4670_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4668_, v___x_4669_);
lean_dec(v_a_4668_);
return v___x_4670_;
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
v_a_4671_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4667_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4667_);
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
case 2:
{
lean_object* v_mvarId_4679_; lean_object* v___x_4680_; 
v_mvarId_4679_ = lean_ctor_get(v_x_4660_, 0);
lean_inc(v_mvarId_4679_);
lean_dec_ref(v_x_4660_);
v___x_4680_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4679_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref(v___x_4680_);
v___x_4682_ = lean_unsigned_to_nat(0u);
v___x_4683_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4681_, v___x_4682_);
lean_dec(v_a_4681_);
return v___x_4683_;
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
v_a_4684_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4680_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4680_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
case 3:
{
uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
lean_dec_ref(v_x_4660_);
v___x_4692_ = 1;
v___x_4693_ = lean_box(v___x_4692_);
v___x_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4693_);
return v___x_4694_;
}
case 4:
{
lean_object* v_declName_4695_; lean_object* v_us_4696_; lean_object* v___x_4697_; 
v_declName_4695_ = lean_ctor_get(v_x_4660_, 0);
lean_inc(v_declName_4695_);
v_us_4696_ = lean_ctor_get(v_x_4660_, 1);
lean_inc(v_us_4696_);
lean_dec_ref(v_x_4660_);
v___x_4697_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4695_, v_us_4696_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref(v___x_4697_);
v___x_4699_ = lean_unsigned_to_nat(0u);
v___x_4700_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4698_, v___x_4699_);
lean_dec(v_a_4698_);
return v___x_4700_;
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
v_a_4701_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4697_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4697_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
case 5:
{
lean_object* v_fn_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v_fn_4709_ = lean_ctor_get(v_x_4660_, 0);
lean_inc_ref(v_fn_4709_);
lean_dec_ref(v_x_4660_);
v___x_4710_ = lean_unsigned_to_nat(1u);
v___x_4711_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4709_, v___x_4710_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
return v___x_4711_;
}
case 6:
{
uint8_t v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
lean_dec_ref(v_x_4660_);
v___x_4712_ = 0;
v___x_4713_ = lean_box(v___x_4712_);
v___x_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4713_);
return v___x_4714_;
}
case 7:
{
uint8_t v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
lean_dec_ref(v_x_4660_);
v___x_4715_ = 1;
v___x_4716_ = lean_box(v___x_4715_);
v___x_4717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4716_);
return v___x_4717_;
}
case 8:
{
lean_object* v_body_4718_; 
v_body_4718_ = lean_ctor_get(v_x_4660_, 3);
lean_inc_ref(v_body_4718_);
lean_dec_ref(v_x_4660_);
v_x_4660_ = v_body_4718_;
goto _start;
}
case 9:
{
uint8_t v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
lean_dec_ref(v_x_4660_);
v___x_4720_ = 0;
v___x_4721_ = lean_box(v___x_4720_);
v___x_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4721_);
return v___x_4722_;
}
case 10:
{
lean_object* v_expr_4723_; 
v_expr_4723_ = lean_ctor_get(v_x_4660_, 1);
lean_inc_ref(v_expr_4723_);
lean_dec_ref(v_x_4660_);
v_x_4660_ = v_expr_4723_;
goto _start;
}
default: 
{
uint8_t v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
lean_dec_ref(v_x_4660_);
v___x_4725_ = 2;
v___x_4726_ = lean_box(v___x_4725_);
v___x_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
return v___x_4727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l_Lean_Meta_isTypeQuick(v_x_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v___x_4741_; 
lean_inc_ref(v_e_4735_);
v___x_4741_ = l_Lean_Meta_isTypeQuick(v_e_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4791_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4744_ = v___x_4741_;
v_isShared_4745_ = v_isSharedCheck_4791_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4741_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4791_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
uint8_t v___x_4746_; 
v___x_4746_ = lean_unbox(v_a_4742_);
lean_dec(v_a_4742_);
switch(v___x_4746_)
{
case 0:
{
uint8_t v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4750_; 
lean_dec_ref(v_e_4735_);
v___x_4747_ = 0;
v___x_4748_ = lean_box(v___x_4747_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 0, v___x_4748_);
v___x_4750_ = v___x_4744_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4748_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
case 1:
{
uint8_t v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4755_; 
lean_dec_ref(v_e_4735_);
v___x_4752_ = 1;
v___x_4753_ = lean_box(v___x_4752_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 0, v___x_4753_);
v___x_4755_ = v___x_4744_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
default: 
{
lean_object* v___x_4757_; 
lean_del_object(v___x_4744_);
lean_inc(v_a_4739_);
lean_inc_ref(v_a_4738_);
lean_inc(v_a_4737_);
lean_inc_ref(v_a_4736_);
v___x_4757_ = lean_infer_type(v_e_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v___x_4759_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref(v___x_4757_);
v___x_4759_ = l_Lean_Meta_whnfD(v_a_4758_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4774_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4774_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4774_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
if (lean_obj_tag(v_a_4760_) == 3)
{
uint8_t v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4767_; 
lean_dec_ref(v_a_4760_);
v___x_4764_ = 1;
v___x_4765_ = lean_box(v___x_4764_);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v___x_4765_);
v___x_4767_ = v___x_4762_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4765_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
else
{
uint8_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4772_; 
lean_dec(v_a_4760_);
v___x_4769_ = 0;
v___x_4770_ = lean_box(v___x_4769_);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v___x_4770_);
v___x_4772_ = v___x_4762_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
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
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
v_a_4775_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4759_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4759_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
v_a_4783_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4757_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4757_);
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
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec_ref(v_e_4735_);
v_a_4792_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4741_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4741_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Lean_Meta_isType(v_e_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4807_){
_start:
{
switch(lean_obj_tag(v_x_4807_))
{
case 7:
{
lean_object* v_body_4808_; 
v_body_4808_ = lean_ctor_get(v_x_4807_, 2);
v_x_4807_ = v_body_4808_;
goto _start;
}
case 3:
{
lean_object* v_u_4810_; lean_object* v___x_4811_; 
v_u_4810_ = lean_ctor_get(v_x_4807_, 0);
lean_inc(v_u_4810_);
v___x_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4811_, 0, v_u_4810_);
return v___x_4811_;
}
default: 
{
lean_object* v___x_4812_; 
v___x_4812_ = lean_box(0);
return v___x_4812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4813_);
lean_dec_ref(v_x_4813_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4815_, lean_object* v_body_4816_, lean_object* v_x_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4815_, v_body_4816_, v_x_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec(v___y_4819_);
lean_dec_ref(v___y_4818_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4826_, lean_object* v_xs_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
switch(lean_obj_tag(v_type_4826_))
{
case 3:
{
lean_object* v_u_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
lean_dec_ref(v_xs_4827_);
v_u_4833_ = lean_ctor_get(v_type_4826_, 0);
lean_inc(v_u_4833_);
lean_dec_ref(v_type_4826_);
v___x_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4834_, 0, v_u_4833_);
v___x_4835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4834_);
return v___x_4835_;
}
case 7:
{
lean_object* v_binderName_4836_; lean_object* v_binderType_4837_; lean_object* v_body_4838_; uint8_t v_binderInfo_4839_; lean_object* v___f_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v_binderName_4836_ = lean_ctor_get(v_type_4826_, 0);
lean_inc(v_binderName_4836_);
v_binderType_4837_ = lean_ctor_get(v_type_4826_, 1);
lean_inc_ref(v_binderType_4837_);
v_body_4838_ = lean_ctor_get(v_type_4826_, 2);
lean_inc_ref(v_body_4838_);
v_binderInfo_4839_ = lean_ctor_get_uint8(v_type_4826_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_4826_);
lean_inc_ref(v_xs_4827_);
v___f_4840_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4840_, 0, v_xs_4827_);
lean_closure_set(v___f_4840_, 1, v_body_4838_);
v___x_4841_ = lean_expr_instantiate_rev(v_binderType_4837_, v_xs_4827_);
lean_dec_ref(v_xs_4827_);
lean_dec_ref(v_binderType_4837_);
v___x_4842_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4836_, v_binderInfo_4839_, v___x_4841_, v___f_4840_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
return v___x_4842_;
}
default: 
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = lean_expr_instantiate_rev(v_type_4826_, v_xs_4827_);
lean_dec_ref(v_xs_4827_);
lean_dec_ref(v_type_4826_);
v___x_4844_ = l_Lean_Meta_whnfD(v___x_4843_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4860_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4847_ = v___x_4844_;
v_isShared_4848_ = v_isSharedCheck_4860_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4844_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4860_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
switch(lean_obj_tag(v_a_4845_))
{
case 3:
{
lean_object* v_u_4849_; lean_object* v___x_4850_; lean_object* v___x_4852_; 
v_u_4849_ = lean_ctor_get(v_a_4845_, 0);
lean_inc(v_u_4849_);
lean_dec_ref(v_a_4845_);
v___x_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4850_, 0, v_u_4849_);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4850_);
v___x_4852_ = v___x_4847_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
case 7:
{
lean_object* v___x_4854_; 
lean_del_object(v___x_4847_);
v___x_4854_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4826_ = v_a_4845_;
v_xs_4827_ = v___x_4854_;
goto _start;
}
default: 
{
lean_object* v___x_4856_; lean_object* v___x_4858_; 
lean_dec(v_a_4845_);
v___x_4856_ = lean_box(0);
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v___x_4856_);
v___x_4858_ = v___x_4847_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
v_a_4861_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4844_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4844_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4869_, lean_object* v_body_4870_, lean_object* v_x_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_array_push(v_xs_4869_, v_x_4871_);
v___x_4878_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4870_, v___x_4877_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4879_, lean_object* v_xs_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4879_, v_xs_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4887_, lean_object* v_cache_4888_, lean_object* v_a_x3f_4889_){
_start:
{
lean_object* v___x_4891_; lean_object* v_mctx_4892_; lean_object* v_zetaDeltaFVarIds_4893_; lean_object* v_postponed_4894_; lean_object* v_diag_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4905_; 
v___x_4891_ = lean_st_ref_take(v_a_4887_);
v_mctx_4892_ = lean_ctor_get(v___x_4891_, 0);
v_zetaDeltaFVarIds_4893_ = lean_ctor_get(v___x_4891_, 2);
v_postponed_4894_ = lean_ctor_get(v___x_4891_, 3);
v_diag_4895_ = lean_ctor_get(v___x_4891_, 4);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4905_ == 0)
{
lean_object* v_unused_4906_; 
v_unused_4906_ = lean_ctor_get(v___x_4891_, 1);
lean_dec(v_unused_4906_);
v___x_4897_ = v___x_4891_;
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_diag_4895_);
lean_inc(v_postponed_4894_);
lean_inc(v_zetaDeltaFVarIds_4893_);
lean_inc(v_mctx_4892_);
lean_dec(v___x_4891_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4905_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 1, v_cache_4888_);
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_mctx_4892_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_cache_4888_);
lean_ctor_set(v_reuseFailAlloc_4904_, 2, v_zetaDeltaFVarIds_4893_);
lean_ctor_set(v_reuseFailAlloc_4904_, 3, v_postponed_4894_);
lean_ctor_set(v_reuseFailAlloc_4904_, 4, v_diag_4895_);
v___x_4900_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4901_ = lean_st_ref_set(v_a_4887_, v___x_4900_);
v___x_4902_ = lean_box(0);
v___x_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4902_);
return v___x_4903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4907_, lean_object* v_cache_4908_, lean_object* v_a_x3f_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4907_, v_cache_4908_, v_a_x3f_4909_);
lean_dec(v_a_x3f_4909_);
lean_dec(v_a_4907_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
lean_object* v___x_4918_; 
v___x_4918_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4912_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v___x_4919_; lean_object* v_cache_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4919_ = lean_st_ref_get(v_a_4914_);
v_cache_4920_ = lean_ctor_get(v___x_4919_, 1);
lean_inc_ref(v_cache_4920_);
lean_dec(v___x_4919_);
v___x_4921_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v___x_4922_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4912_, v___x_4921_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4939_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4925_ = v___x_4922_;
v_isShared_4926_ = v_isSharedCheck_4939_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4922_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4939_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
lean_inc(v_a_4923_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set_tag(v___x_4925_, 1);
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
v___x_4929_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4914_, v_cache_4920_, v___x_4928_);
lean_dec_ref(v___x_4928_);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4936_ == 0)
{
lean_object* v_unused_4937_; 
v_unused_4937_ = lean_ctor_get(v___x_4929_, 0);
lean_dec(v_unused_4937_);
v___x_4931_ = v___x_4929_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_dec(v___x_4929_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 0, v_a_4923_);
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4923_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
v_a_4940_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4940_);
lean_dec_ref(v___x_4922_);
v___x_4941_ = lean_box(0);
v___x_4942_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4914_, v_cache_4920_, v___x_4941_);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_4949_ == 0)
{
lean_object* v_unused_4950_; 
v_unused_4950_ = lean_ctor_get(v___x_4942_, 0);
lean_dec(v_unused_4950_);
v___x_4944_ = v___x_4942_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_dec(v___x_4942_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
lean_ctor_set_tag(v___x_4944_, 1);
lean_ctor_set(v___x_4944_, 0, v_a_4940_);
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4940_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
else
{
lean_object* v___x_4951_; 
lean_dec_ref(v_type_4912_);
v___x_4951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4918_);
return v___x_4951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4980_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4968_ = v___x_4965_;
v_isShared_4969_ = v_isSharedCheck_4980_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4965_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4980_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
if (lean_obj_tag(v_a_4966_) == 0)
{
uint8_t v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4970_ = 0;
v___x_4971_ = lean_box(v___x_4970_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v___x_4971_);
v___x_4973_ = v___x_4968_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4971_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
else
{
uint8_t v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4978_; 
lean_dec_ref(v_a_4966_);
v___x_4975_ = 1;
v___x_4976_ = lean_box(v___x_4975_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v___x_4976_);
v___x_4978_ = v___x_4968_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4976_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
v_a_4981_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4965_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4965_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Lean_Meta_isTypeFormerType(v_type_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
return v_res_4995_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_4996_, lean_object* v_x_4997_){
_start:
{
if (lean_obj_tag(v_x_4996_) == 0)
{
if (lean_obj_tag(v_x_4997_) == 0)
{
uint8_t v___x_4998_; 
v___x_4998_ = 1;
return v___x_4998_;
}
else
{
uint8_t v___x_4999_; 
v___x_4999_ = 0;
return v___x_4999_;
}
}
else
{
if (lean_obj_tag(v_x_4997_) == 0)
{
uint8_t v___x_5000_; 
v___x_5000_ = 0;
return v___x_5000_;
}
else
{
lean_object* v_val_5001_; lean_object* v_val_5002_; uint8_t v___x_5003_; 
v_val_5001_ = lean_ctor_get(v_x_4996_, 0);
v_val_5002_ = lean_ctor_get(v_x_4997_, 0);
v___x_5003_ = lean_level_eq(v_val_5001_, v_val_5002_);
return v___x_5003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_5004_, lean_object* v_x_5005_){
_start:
{
uint8_t v_res_5006_; lean_object* v_r_5007_; 
v_res_5006_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_5004_, v_x_5005_);
lean_dec(v_x_5005_);
lean_dec(v_x_5004_);
v_r_5007_ = lean_box(v_res_5006_);
return v_r_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Lean_Meta_typeFormerTypeLevel(v_type_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5027_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5019_ = v___x_5016_;
v_isShared_5020_ = v_isSharedCheck_5027_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5016_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5027_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5021_; uint8_t v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5025_; 
v___x_5021_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_5022_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_5017_, v___x_5021_);
lean_dec(v_a_5017_);
v___x_5023_ = lean_box(v___x_5022_);
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 0, v___x_5023_);
v___x_5025_ = v___x_5019_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5023_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
v_a_5028_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_5016_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_5016_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Lean_Meta_isPropFormerType(v_type_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_){
_start:
{
lean_object* v___x_5049_; 
lean_inc(v_a_5047_);
lean_inc_ref(v_a_5046_);
lean_inc(v_a_5045_);
lean_inc_ref(v_a_5044_);
v___x_5049_ = lean_infer_type(v_e_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref(v___x_5049_);
v___x_5051_ = l_Lean_Meta_isTypeFormerType(v_a_5050_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
return v___x_5051_;
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
v_a_5052_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5054_ = v___x_5049_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5049_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Meta_isTypeFormer(v_e_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_5067_, lean_object* v_maxFVars_x3f_5068_, lean_object* v_k_5069_, uint8_t v_cleanupAnnotations_5070_, uint8_t v_whnfType_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v___f_5077_; lean_object* v___x_5078_; 
v___f_5077_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_5077_, 0, v_k_5069_);
v___x_5078_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_5067_, v_maxFVars_x3f_5068_, v___f_5077_, v_cleanupAnnotations_5070_, v_whnfType_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_a_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5086_; 
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5086_ == 0)
{
v___x_5081_ = v___x_5078_;
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_a_5079_);
lean_dec(v___x_5078_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5086_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5084_; 
if (v_isShared_5082_ == 0)
{
v___x_5084_ = v___x_5081_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
else
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
v_a_5087_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5078_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5078_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_5095_, lean_object* v_maxFVars_x3f_5096_, lean_object* v_k_5097_, lean_object* v_cleanupAnnotations_5098_, lean_object* v_whnfType_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5105_; uint8_t v_whnfType_boxed_5106_; lean_object* v_res_5107_; 
v_cleanupAnnotations_boxed_5105_ = lean_unbox(v_cleanupAnnotations_5098_);
v_whnfType_boxed_5106_ = lean_unbox(v_whnfType_5099_);
v_res_5107_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5095_, v_maxFVars_x3f_5096_, v_k_5097_, v_cleanupAnnotations_boxed_5105_, v_whnfType_boxed_5106_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_5108_, lean_object* v_type_5109_, lean_object* v_maxFVars_x3f_5110_, lean_object* v_k_5111_, uint8_t v_cleanupAnnotations_5112_, uint8_t v_whnfType_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v___x_5119_; 
v___x_5119_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5109_, v_maxFVars_x3f_5110_, v_k_5111_, v_cleanupAnnotations_5112_, v_whnfType_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_5120_, lean_object* v_type_5121_, lean_object* v_maxFVars_x3f_5122_, lean_object* v_k_5123_, lean_object* v_cleanupAnnotations_5124_, lean_object* v_whnfType_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_5131_; uint8_t v_whnfType_boxed_5132_; lean_object* v_res_5133_; 
v_cleanupAnnotations_boxed_5131_ = lean_unbox(v_cleanupAnnotations_5124_);
v_whnfType_boxed_5132_ = lean_unbox(v_whnfType_5125_);
v_res_5133_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_5120_, v_type_5121_, v_maxFVars_x3f_5122_, v_k_5123_, v_cleanupAnnotations_boxed_5131_, v_whnfType_boxed_5132_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
lean_dec(v___y_5127_);
lean_dec_ref(v___y_5126_);
return v_res_5133_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_5134_, lean_object* v_as_5135_, size_t v_i_5136_, size_t v_stop_5137_){
_start:
{
uint8_t v___x_5138_; 
v___x_5138_ = lean_usize_dec_eq(v_i_5136_, v_stop_5137_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; uint8_t v___x_5140_; 
v___x_5139_ = lean_array_uget_borrowed(v_as_5135_, v_i_5136_);
v___x_5140_ = lean_expr_eqv(v_a_5134_, v___x_5139_);
if (v___x_5140_ == 0)
{
size_t v___x_5141_; size_t v___x_5142_; 
v___x_5141_ = ((size_t)1ULL);
v___x_5142_ = lean_usize_add(v_i_5136_, v___x_5141_);
v_i_5136_ = v___x_5142_;
goto _start;
}
else
{
return v___x_5140_;
}
}
else
{
uint8_t v___x_5144_; 
v___x_5144_ = 0;
return v___x_5144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_5145_, lean_object* v_as_5146_, lean_object* v_i_5147_, lean_object* v_stop_5148_){
_start:
{
size_t v_i_boxed_5149_; size_t v_stop_boxed_5150_; uint8_t v_res_5151_; lean_object* v_r_5152_; 
v_i_boxed_5149_ = lean_unbox_usize(v_i_5147_);
lean_dec(v_i_5147_);
v_stop_boxed_5150_ = lean_unbox_usize(v_stop_5148_);
lean_dec(v_stop_5148_);
v_res_5151_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5145_, v_as_5146_, v_i_boxed_5149_, v_stop_boxed_5150_);
lean_dec_ref(v_as_5146_);
lean_dec_ref(v_a_5145_);
v_r_5152_ = lean_box(v_res_5151_);
return v_r_5152_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_5153_, lean_object* v_a_5154_){
_start:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; uint8_t v___x_5157_; 
v___x_5155_ = lean_unsigned_to_nat(0u);
v___x_5156_ = lean_array_get_size(v_as_5153_);
v___x_5157_ = lean_nat_dec_lt(v___x_5155_, v___x_5156_);
if (v___x_5157_ == 0)
{
return v___x_5157_;
}
else
{
if (v___x_5157_ == 0)
{
return v___x_5157_;
}
else
{
size_t v___x_5158_; size_t v___x_5159_; uint8_t v___x_5160_; 
v___x_5158_ = ((size_t)0ULL);
v___x_5159_ = lean_usize_of_nat(v___x_5156_);
v___x_5160_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_5154_, v_as_5153_, v___x_5158_, v___x_5159_);
return v___x_5160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_5161_, lean_object* v_a_5162_){
_start:
{
uint8_t v_res_5163_; lean_object* v_r_5164_; 
v_res_5163_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_5161_, v_a_5162_);
lean_dec_ref(v_a_5162_);
lean_dec_ref(v_as_5161_);
v_r_5164_ = lean_box(v_res_5163_);
return v_r_5164_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_5165_, lean_object* v_e_5166_){
_start:
{
uint8_t v___x_5167_; lean_object* v_d_5169_; lean_object* v_b_5170_; 
v___x_5167_ = l_Lean_Expr_hasFVar(v_e_5166_);
if (v___x_5167_ == 0)
{
lean_dec_ref(v_e_5166_);
return v___x_5167_;
}
else
{
switch(lean_obj_tag(v_e_5166_))
{
case 7:
{
lean_object* v_binderType_5173_; lean_object* v_body_5174_; 
v_binderType_5173_ = lean_ctor_get(v_e_5166_, 1);
lean_inc_ref(v_binderType_5173_);
v_body_5174_ = lean_ctor_get(v_e_5166_, 2);
lean_inc_ref(v_body_5174_);
lean_dec_ref(v_e_5166_);
v_d_5169_ = v_binderType_5173_;
v_b_5170_ = v_body_5174_;
goto v___jp_5168_;
}
case 6:
{
lean_object* v_binderType_5175_; lean_object* v_body_5176_; 
v_binderType_5175_ = lean_ctor_get(v_e_5166_, 1);
lean_inc_ref(v_binderType_5175_);
v_body_5176_ = lean_ctor_get(v_e_5166_, 2);
lean_inc_ref(v_body_5176_);
lean_dec_ref(v_e_5166_);
v_d_5169_ = v_binderType_5175_;
v_b_5170_ = v_body_5176_;
goto v___jp_5168_;
}
case 10:
{
lean_object* v_expr_5177_; 
v_expr_5177_ = lean_ctor_get(v_e_5166_, 1);
lean_inc_ref(v_expr_5177_);
lean_dec_ref(v_e_5166_);
v_e_5166_ = v_expr_5177_;
goto _start;
}
case 8:
{
lean_object* v_type_5179_; lean_object* v_value_5180_; lean_object* v_body_5181_; uint8_t v___x_5182_; 
v_type_5179_ = lean_ctor_get(v_e_5166_, 1);
lean_inc_ref(v_type_5179_);
v_value_5180_ = lean_ctor_get(v_e_5166_, 2);
lean_inc_ref(v_value_5180_);
v_body_5181_ = lean_ctor_get(v_e_5166_, 3);
lean_inc_ref(v_body_5181_);
lean_dec_ref(v_e_5166_);
v___x_5182_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5165_, v_type_5179_);
if (v___x_5182_ == 0)
{
uint8_t v___x_5183_; 
v___x_5183_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5165_, v_value_5180_);
if (v___x_5183_ == 0)
{
v_e_5166_ = v_body_5181_;
goto _start;
}
else
{
lean_dec_ref(v_body_5181_);
return v___x_5167_;
}
}
else
{
lean_dec_ref(v_body_5181_);
lean_dec_ref(v_value_5180_);
return v___x_5167_;
}
}
case 5:
{
lean_object* v_fn_5185_; lean_object* v_arg_5186_; uint8_t v___x_5187_; 
v_fn_5185_ = lean_ctor_get(v_e_5166_, 0);
lean_inc_ref(v_fn_5185_);
v_arg_5186_ = lean_ctor_get(v_e_5166_, 1);
lean_inc_ref(v_arg_5186_);
lean_dec_ref(v_e_5166_);
v___x_5187_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5165_, v_fn_5185_);
if (v___x_5187_ == 0)
{
v_e_5166_ = v_arg_5186_;
goto _start;
}
else
{
lean_dec_ref(v_arg_5186_);
return v___x_5167_;
}
}
case 11:
{
lean_object* v_struct_5189_; 
v_struct_5189_ = lean_ctor_get(v_e_5166_, 2);
lean_inc_ref(v_struct_5189_);
lean_dec_ref(v_e_5166_);
v_e_5166_ = v_struct_5189_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_5191_; lean_object* v___x_5192_; uint8_t v___x_5193_; 
v_fvarId_5191_ = lean_ctor_get(v_e_5166_, 0);
lean_inc(v_fvarId_5191_);
lean_dec_ref(v_e_5166_);
v___x_5192_ = l_Lean_Expr_fvar___override(v_fvarId_5191_);
v___x_5193_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_5165_, v___x_5192_);
lean_dec_ref(v___x_5192_);
return v___x_5193_;
}
default: 
{
uint8_t v___x_5194_; 
lean_dec_ref(v_e_5166_);
v___x_5194_ = 0;
return v___x_5194_;
}
}
}
v___jp_5168_:
{
uint8_t v___x_5171_; 
v___x_5171_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5165_, v_d_5169_);
if (v___x_5171_ == 0)
{
v_e_5166_ = v_b_5170_;
goto _start;
}
else
{
lean_dec_ref(v_b_5170_);
return v___x_5167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_5195_, lean_object* v_e_5196_){
_start:
{
uint8_t v_res_5197_; lean_object* v_r_5198_; 
v_res_5197_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5195_, v_e_5196_);
lean_dec_ref(v_xs_5195_);
v_r_5198_ = lean_box(v_res_5197_);
return v_r_5198_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5201_ = l_Lean_stringToMessageData(v___x_5200_);
return v___x_5201_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5203_; lean_object* v___x_5204_; 
v___x_5203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5204_ = l_Lean_stringToMessageData(v___x_5203_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5205_, lean_object* v_type_5206_, lean_object* v_as_5207_, size_t v_sz_5208_, size_t v_i_5209_, lean_object* v_b_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v_a_5217_; uint8_t v___x_5221_; 
v___x_5221_ = lean_usize_dec_lt(v_i_5209_, v_sz_5208_);
if (v___x_5221_ == 0)
{
lean_object* v___x_5222_; 
lean_dec_ref(v_type_5206_);
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v_b_5210_);
return v___x_5222_;
}
else
{
lean_object* v___x_5223_; lean_object* v_a_5224_; uint8_t v___x_5225_; 
v___x_5223_ = lean_box(0);
v_a_5224_ = lean_array_uget_borrowed(v_as_5207_, v_i_5209_);
lean_inc(v_a_5224_);
v___x_5225_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5205_, v_a_5224_);
if (v___x_5225_ == 0)
{
v_a_5217_ = v___x_5223_;
goto v___jp_5216_;
}
else
{
lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
v___x_5226_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5224_);
v___x_5227_ = l_Lean_MessageData_ofExpr(v_a_5224_);
v___x_5228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5226_);
lean_ctor_set(v___x_5228_, 1, v___x_5227_);
v___x_5229_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5228_);
lean_ctor_set(v___x_5230_, 1, v___x_5229_);
lean_inc_ref(v_type_5206_);
v___x_5231_ = l_Lean_MessageData_ofExpr(v_type_5206_);
v___x_5232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5230_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
v___x_5233_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5232_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_dec_ref(v___x_5233_);
v_a_5217_ = v___x_5223_;
goto v___jp_5216_;
}
else
{
lean_dec_ref(v_type_5206_);
return v___x_5233_;
}
}
}
v___jp_5216_:
{
size_t v___x_5218_; size_t v___x_5219_; 
v___x_5218_ = ((size_t)1ULL);
v___x_5219_ = lean_usize_add(v_i_5209_, v___x_5218_);
v_i_5209_ = v___x_5219_;
v_b_5210_ = v_a_5217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5234_, lean_object* v_type_5235_, lean_object* v_as_5236_, lean_object* v_sz_5237_, lean_object* v_i_5238_, lean_object* v_b_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
size_t v_sz_boxed_5245_; size_t v_i_boxed_5246_; lean_object* v_res_5247_; 
v_sz_boxed_5245_ = lean_unbox_usize(v_sz_5237_);
lean_dec(v_sz_5237_);
v_i_boxed_5246_ = lean_unbox_usize(v_i_5238_);
lean_dec(v_i_5238_);
v_res_5247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5234_, v_type_5235_, v_as_5236_, v_sz_boxed_5245_, v_i_boxed_5246_, v_b_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec_ref(v_as_5236_);
lean_dec_ref(v_xs_5234_);
return v_res_5247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5248_, size_t v_i_5249_, lean_object* v_bs_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
uint8_t v___x_5256_; 
v___x_5256_ = lean_usize_dec_lt(v_i_5249_, v_sz_5248_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; 
v___x_5257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5257_, 0, v_bs_5250_);
return v___x_5257_;
}
else
{
lean_object* v_v_5258_; lean_object* v___x_5259_; 
v_v_5258_ = lean_array_uget_borrowed(v_bs_5250_, v_i_5249_);
lean_inc(v___y_5254_);
lean_inc_ref(v___y_5253_);
lean_inc(v___y_5252_);
lean_inc_ref(v___y_5251_);
lean_inc(v_v_5258_);
v___x_5259_ = lean_infer_type(v_v_5258_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
if (lean_obj_tag(v___x_5259_) == 0)
{
lean_object* v_a_5260_; lean_object* v___x_5261_; lean_object* v_bs_x27_5262_; size_t v___x_5263_; size_t v___x_5264_; lean_object* v___x_5265_; 
v_a_5260_ = lean_ctor_get(v___x_5259_, 0);
lean_inc(v_a_5260_);
lean_dec_ref(v___x_5259_);
v___x_5261_ = lean_unsigned_to_nat(0u);
v_bs_x27_5262_ = lean_array_uset(v_bs_5250_, v_i_5249_, v___x_5261_);
v___x_5263_ = ((size_t)1ULL);
v___x_5264_ = lean_usize_add(v_i_5249_, v___x_5263_);
v___x_5265_ = lean_array_uset(v_bs_x27_5262_, v_i_5249_, v_a_5260_);
v_i_5249_ = v___x_5264_;
v_bs_5250_ = v___x_5265_;
goto _start;
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
lean_dec_ref(v_bs_5250_);
v_a_5267_ = lean_ctor_get(v___x_5259_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5259_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5259_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5259_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5275_, lean_object* v_i_5276_, lean_object* v_bs_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
size_t v_sz_boxed_5283_; size_t v_i_boxed_5284_; lean_object* v_res_5285_; 
v_sz_boxed_5283_ = lean_unbox_usize(v_sz_5275_);
lean_dec(v_sz_5275_);
v_i_boxed_5284_ = lean_unbox_usize(v_i_5276_);
lean_dec(v_i_5276_);
v_res_5285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5283_, v_i_boxed_5284_, v_bs_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
return v_res_5285_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5288_ = l_Lean_stringToMessageData(v___x_5287_);
return v___x_5288_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5290_; lean_object* v___x_5291_; 
v___x_5290_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5291_ = l_Lean_stringToMessageData(v___x_5290_);
return v___x_5291_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5293_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5294_ = l_Lean_stringToMessageData(v___x_5293_);
return v___x_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5295_, lean_object* v_n_5296_, lean_object* v_xs_5297_, lean_object* v_x_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v___x_5328_; uint8_t v___x_5329_; 
v___x_5328_ = lean_array_get_size(v_xs_5297_);
v___x_5329_ = lean_nat_dec_eq(v___x_5328_, v_n_5296_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
lean_dec_ref(v_xs_5297_);
v___x_5330_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5331_ = l_Lean_MessageData_ofExpr(v_type_5295_);
v___x_5332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5330_);
lean_ctor_set(v___x_5332_, 1, v___x_5331_);
v___x_5333_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5332_);
lean_ctor_set(v___x_5334_, 1, v___x_5333_);
v___x_5335_ = l_Nat_reprFast(v_n_5296_);
v___x_5336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5335_);
v___x_5337_ = l_Lean_MessageData_ofFormat(v___x_5336_);
v___x_5338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5334_);
lean_ctor_set(v___x_5338_, 1, v___x_5337_);
v___x_5339_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5338_);
lean_ctor_set(v___x_5340_, 1, v___x_5339_);
v___x_5341_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5340_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v___x_5341_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5341_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
else
{
lean_dec(v_n_5296_);
goto v___jp_5304_;
}
v___jp_5304_:
{
size_t v_sz_5305_; size_t v___x_5306_; lean_object* v___x_5307_; 
v_sz_5305_ = lean_array_size(v_xs_5297_);
v___x_5306_ = ((size_t)0ULL);
lean_inc_ref(v_xs_5297_);
v___x_5307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5305_, v___x_5306_, v_xs_5297_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5309_; size_t v_sz_5310_; lean_object* v___x_5311_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref(v___x_5307_);
v___x_5309_ = lean_box(0);
v_sz_5310_ = lean_array_size(v_a_5308_);
v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5297_, v_type_5295_, v_a_5308_, v_sz_5310_, v___x_5306_, v___x_5309_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
lean_dec_ref(v_xs_5297_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5318_; 
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5318_ == 0)
{
lean_object* v_unused_5319_; 
v_unused_5319_ = lean_ctor_get(v___x_5311_, 0);
lean_dec(v_unused_5319_);
v___x_5313_ = v___x_5311_;
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
else
{
lean_dec(v___x_5311_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v_a_5308_);
v___x_5316_ = v___x_5313_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5308_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
lean_dec(v_a_5308_);
v_a_5320_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5311_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5311_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
}
}
else
{
lean_dec_ref(v_xs_5297_);
lean_dec_ref(v_type_5295_);
return v___x_5307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5350_, lean_object* v_n_5351_, lean_object* v_xs_5352_, lean_object* v_x_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_){
_start:
{
lean_object* v_res_5359_; 
v_res_5359_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5350_, v_n_5351_, v_xs_5352_, v_x_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec_ref(v_x_5353_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5360_, lean_object* v_type_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_){
_start:
{
lean_object* v___f_5367_; lean_object* v___x_5368_; uint8_t v___x_5369_; lean_object* v___x_5370_; 
lean_inc(v_n_5360_);
lean_inc_ref(v_type_5361_);
v___f_5367_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5367_, 0, v_type_5361_);
lean_closure_set(v___f_5367_, 1, v_n_5360_);
v___x_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5368_, 0, v_n_5360_);
v___x_5369_ = 0;
v___x_5370_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5361_, v___x_5368_, v___f_5367_, v___x_5369_, v___x_5369_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_);
return v___x_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5371_, lean_object* v_type_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l_Lean_Meta_arrowDomainsN(v_n_5371_, v_type_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_);
lean_dec(v_a_5376_);
lean_dec_ref(v_a_5375_);
lean_dec(v_a_5374_);
lean_dec_ref(v_a_5373_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5379_, lean_object* v_e_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v___x_5386_; 
lean_inc(v_a_5384_);
lean_inc_ref(v_a_5383_);
lean_inc(v_a_5382_);
lean_inc_ref(v_a_5381_);
v___x_5386_ = lean_infer_type(v_e_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v_a_5387_; lean_object* v___x_5388_; 
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref(v___x_5386_);
v___x_5388_ = l_Lean_Meta_arrowDomainsN(v_n_5379_, v_a_5387_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_);
return v___x_5388_;
}
else
{
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
lean_dec(v_n_5379_);
v_a_5389_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5386_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5386_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5397_, lean_object* v_e_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Lean_Meta_inferArgumentTypesN(v_n_5397_, v_e_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_);
lean_dec(v_a_5402_);
lean_dec_ref(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
return v_res_5404_;
}
}
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
