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
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
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
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
uint8_t l_Lean_Meta_instDecidableEqProjReductionKind(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint8_t l_Lean_Level_isNeverZero(lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_throwUnknown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mkExprConfigCacheKey___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_expr_consume_type_annotations(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6_value;
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
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected bound variable "};
static const lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0 = (const lean_object*)&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(lean_object* v_msg_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___f_11_; lean_object* v___f_12_; lean_object* v___f_13_; lean_object* v___f_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_6110__overap_23_; lean_object* v___x_24_; 
v___f_10_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__0));
v___f_11_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__1));
v___f_12_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__2));
v___f_13_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__3));
v___f_14_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__4));
v___f_15_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__5));
v___f_16_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3___closed__6));
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___f_10_);
lean_ctor_set(v___x_17_, 1, v___f_11_);
v___x_18_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___f_12_);
lean_ctor_set(v___x_18_, 2, v___f_13_);
lean_ctor_set(v___x_18_, 3, v___f_14_);
lean_ctor_set(v___x_18_, 4, v___f_15_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___f_16_);
v___x_20_ = l_Lean_MonadStateCacheT_instMonad___redArg(v___x_19_);
v___x_21_ = l_Lean_instInhabitedExpr;
v___x_22_ = l_instInhabitedOfMonad___redArg(v___x_20_, v___x_21_);
v___x_6110__overap_23_ = lean_panic_fn(v___x_22_, v_msg_8_);
v___x_24_ = lean_apply_1(v___x_6110__overap_23_, v___y_9_);
return v___x_24_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(lean_object* v_a_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
uint8_t v___x_27_; 
v___x_27_ = 0;
return v___x_27_;
}
else
{
lean_object* v_key_28_; lean_object* v_tail_29_; uint8_t v___y_31_; lean_object* v_fst_33_; lean_object* v_snd_34_; lean_object* v_fst_35_; lean_object* v_snd_36_; uint8_t v___x_37_; 
v_key_28_ = lean_ctor_get(v_x_26_, 0);
v_tail_29_ = lean_ctor_get(v_x_26_, 2);
v_fst_33_ = lean_ctor_get(v_key_28_, 0);
v_snd_34_ = lean_ctor_get(v_key_28_, 1);
v_fst_35_ = lean_ctor_get(v_a_25_, 0);
v_snd_36_ = lean_ctor_get(v_a_25_, 1);
v___x_37_ = l_Lean_ExprStructEq_beq(v_fst_33_, v_fst_35_);
if (v___x_37_ == 0)
{
v___y_31_ = v___x_37_;
goto v___jp_30_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = lean_nat_dec_eq(v_snd_34_, v_snd_36_);
v___y_31_ = v___x_38_;
goto v___jp_30_;
}
v___jp_30_:
{
if (v___y_31_ == 0)
{
v_x_26_ = v_tail_29_;
goto _start;
}
else
{
return v___y_31_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_39_, lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(v_a_39_, v_x_40_);
lean_dec(v_x_40_);
lean_dec_ref(v_a_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
return v_x_43_;
}
else
{
lean_object* v_key_45_; lean_object* v_value_46_; lean_object* v_tail_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_74_; 
v_key_45_ = lean_ctor_get(v_x_44_, 0);
v_value_46_ = lean_ctor_get(v_x_44_, 1);
v_tail_47_ = lean_ctor_get(v_x_44_, 2);
v_isSharedCheck_74_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_74_ == 0)
{
v___x_49_ = v_x_44_;
v_isShared_50_ = v_isSharedCheck_74_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_tail_47_);
lean_inc(v_value_46_);
lean_inc(v_key_45_);
lean_dec(v_x_44_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_74_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v_fst_51_; lean_object* v_snd_52_; lean_object* v___x_53_; uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v_fold_59_; uint64_t v___x_60_; uint64_t v___x_61_; uint64_t v___x_62_; size_t v___x_63_; size_t v___x_64_; size_t v___x_65_; size_t v___x_66_; size_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v_fst_51_ = lean_ctor_get(v_key_45_, 0);
v_snd_52_ = lean_ctor_get(v_key_45_, 1);
v___x_53_ = lean_array_get_size(v_x_43_);
v___x_54_ = l_Lean_ExprStructEq_hash(v_fst_51_);
v___x_55_ = lean_uint64_of_nat(v_snd_52_);
v___x_56_ = lean_uint64_mix_hash(v___x_54_, v___x_55_);
v___x_57_ = 32ULL;
v___x_58_ = lean_uint64_shift_right(v___x_56_, v___x_57_);
v_fold_59_ = lean_uint64_xor(v___x_56_, v___x_58_);
v___x_60_ = 16ULL;
v___x_61_ = lean_uint64_shift_right(v_fold_59_, v___x_60_);
v___x_62_ = lean_uint64_xor(v_fold_59_, v___x_61_);
v___x_63_ = lean_uint64_to_usize(v___x_62_);
v___x_64_ = lean_usize_of_nat(v___x_53_);
v___x_65_ = ((size_t)1ULL);
v___x_66_ = lean_usize_sub(v___x_64_, v___x_65_);
v___x_67_ = lean_usize_land(v___x_63_, v___x_66_);
v___x_68_ = lean_array_uget_borrowed(v_x_43_, v___x_67_);
lean_inc(v___x_68_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v___x_68_);
v___x_70_ = v___x_49_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_key_45_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_value_46_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v___x_68_);
v___x_70_ = v_reuseFailAlloc_73_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; 
v___x_71_ = lean_array_uset(v_x_43_, v___x_67_, v___x_70_);
v_x_43_ = v___x_71_;
v_x_44_ = v_tail_47_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4___redArg(lean_object* v_i_75_, lean_object* v_source_76_, lean_object* v_target_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_array_get_size(v_source_76_);
v___x_79_ = lean_nat_dec_lt(v_i_75_, v___x_78_);
if (v___x_79_ == 0)
{
lean_dec_ref(v_source_76_);
lean_dec(v_i_75_);
return v_target_77_;
}
else
{
lean_object* v_es_80_; lean_object* v___x_81_; lean_object* v_source_82_; lean_object* v_target_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_es_80_ = lean_array_fget(v_source_76_, v_i_75_);
v___x_81_ = lean_box(0);
v_source_82_ = lean_array_fset(v_source_76_, v_i_75_, v___x_81_);
v_target_83_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7___redArg(v_target_77_, v_es_80_);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_add(v_i_75_, v___x_84_);
lean_dec(v_i_75_);
v_i_75_ = v___x_85_;
v_source_76_ = v_source_82_;
v_target_77_ = v_target_83_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2___redArg(lean_object* v_data_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_nbuckets_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_88_ = lean_array_get_size(v_data_87_);
v___x_89_ = lean_unsigned_to_nat(2u);
v_nbuckets_90_ = lean_nat_mul(v___x_88_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_box(0);
v___x_93_ = lean_mk_array(v_nbuckets_90_, v___x_92_);
v___x_94_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4___redArg(v___x_91_, v_data_87_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(lean_object* v_a_95_, lean_object* v_b_96_, lean_object* v_x_97_){
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
lean_object* v_key_98_; lean_object* v_value_99_; lean_object* v_tail_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_119_; 
v_key_98_ = lean_ctor_get(v_x_97_, 0);
v_value_99_ = lean_ctor_get(v_x_97_, 1);
v_tail_100_ = lean_ctor_get(v_x_97_, 2);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_97_);
if (v_isSharedCheck_119_ == 0)
{
v___x_102_ = v_x_97_;
v_isShared_103_ = v_isSharedCheck_119_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_tail_100_);
lean_inc(v_value_99_);
lean_inc(v_key_98_);
lean_dec(v_x_97_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_119_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
uint8_t v___y_105_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; uint8_t v___x_117_; 
v_fst_113_ = lean_ctor_get(v_key_98_, 0);
v_snd_114_ = lean_ctor_get(v_key_98_, 1);
v_fst_115_ = lean_ctor_get(v_a_95_, 0);
v_snd_116_ = lean_ctor_get(v_a_95_, 1);
v___x_117_ = l_Lean_ExprStructEq_beq(v_fst_113_, v_fst_115_);
if (v___x_117_ == 0)
{
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_eq(v_snd_114_, v_snd_116_);
v___y_105_ = v___x_118_;
goto v___jp_104_;
}
v___jp_104_:
{
if (v___y_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(v_a_95_, v_b_96_, v_tail_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 2, v___x_106_);
v___x_108_ = v___x_102_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_key_98_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_value_99_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v___x_111_; 
lean_dec(v_value_99_);
lean_dec(v_key_98_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v_b_96_);
lean_ctor_set(v___x_102_, 0, v_a_95_);
v___x_111_ = v___x_102_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_95_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_b_96_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_tail_100_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(lean_object* v_m_120_, lean_object* v_a_121_, lean_object* v_b_122_){
_start:
{
lean_object* v_size_123_; lean_object* v_buckets_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_171_; 
v_size_123_ = lean_ctor_get(v_m_120_, 0);
v_buckets_124_ = lean_ctor_get(v_m_120_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_m_120_);
if (v_isSharedCheck_171_ == 0)
{
v___x_126_ = v_m_120_;
v_isShared_127_ = v_isSharedCheck_171_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_buckets_124_);
lean_inc(v_size_123_);
lean_dec(v_m_120_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_171_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_fst_128_; lean_object* v_snd_129_; lean_object* v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v_fold_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v_bkt_145_; uint8_t v___x_146_; 
v_fst_128_ = lean_ctor_get(v_a_121_, 0);
v_snd_129_ = lean_ctor_get(v_a_121_, 1);
v___x_130_ = lean_array_get_size(v_buckets_124_);
v___x_131_ = l_Lean_ExprStructEq_hash(v_fst_128_);
v___x_132_ = lean_uint64_of_nat(v_snd_129_);
v___x_133_ = lean_uint64_mix_hash(v___x_131_, v___x_132_);
v___x_134_ = 32ULL;
v___x_135_ = lean_uint64_shift_right(v___x_133_, v___x_134_);
v_fold_136_ = lean_uint64_xor(v___x_133_, v___x_135_);
v___x_137_ = 16ULL;
v___x_138_ = lean_uint64_shift_right(v_fold_136_, v___x_137_);
v___x_139_ = lean_uint64_xor(v_fold_136_, v___x_138_);
v___x_140_ = lean_uint64_to_usize(v___x_139_);
v___x_141_ = lean_usize_of_nat(v___x_130_);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_sub(v___x_141_, v___x_142_);
v___x_144_ = lean_usize_land(v___x_140_, v___x_143_);
v_bkt_145_ = lean_array_uget_borrowed(v_buckets_124_, v___x_144_);
v___x_146_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(v_a_121_, v_bkt_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v_size_x27_148_; lean_object* v___x_149_; lean_object* v_buckets_x27_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_147_ = lean_unsigned_to_nat(1u);
v_size_x27_148_ = lean_nat_add(v_size_123_, v___x_147_);
lean_dec(v_size_123_);
lean_inc(v_bkt_145_);
v___x_149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_149_, 0, v_a_121_);
lean_ctor_set(v___x_149_, 1, v_b_122_);
lean_ctor_set(v___x_149_, 2, v_bkt_145_);
v_buckets_x27_150_ = lean_array_uset(v_buckets_124_, v___x_144_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(4u);
v___x_152_ = lean_nat_mul(v_size_x27_148_, v___x_151_);
v___x_153_ = lean_unsigned_to_nat(3u);
v___x_154_ = lean_nat_div(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_array_get_size(v_buckets_x27_150_);
v___x_156_ = lean_nat_dec_le(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
if (v___x_156_ == 0)
{
lean_object* v_val_157_; lean_object* v___x_159_; 
v_val_157_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2___redArg(v_buckets_x27_150_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_val_157_);
lean_ctor_set(v___x_126_, 0, v_size_x27_148_);
v___x_159_ = v___x_126_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_size_x27_148_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_val_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_object* v___x_162_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v_buckets_x27_150_);
lean_ctor_set(v___x_126_, 0, v_size_x27_148_);
v___x_162_ = v___x_126_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_size_x27_148_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_buckets_x27_150_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v___x_164_; lean_object* v_buckets_x27_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
lean_inc(v_bkt_145_);
v___x_164_ = lean_box(0);
v_buckets_x27_165_ = lean_array_uset(v_buckets_124_, v___x_144_, v___x_164_);
v___x_166_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(v_a_121_, v_b_122_, v_bkt_145_);
v___x_167_ = lean_array_uset(v_buckets_x27_165_, v___x_144_, v___x_166_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_167_);
v___x_169_ = v___x_126_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_size_123_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(lean_object* v_a_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
else
{
lean_object* v_key_175_; lean_object* v_value_176_; lean_object* v_tail_177_; uint8_t v___y_179_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v_fst_184_; lean_object* v_snd_185_; uint8_t v___x_186_; 
v_key_175_ = lean_ctor_get(v_x_173_, 0);
v_value_176_ = lean_ctor_get(v_x_173_, 1);
v_tail_177_ = lean_ctor_get(v_x_173_, 2);
v_fst_182_ = lean_ctor_get(v_key_175_, 0);
v_snd_183_ = lean_ctor_get(v_key_175_, 1);
v_fst_184_ = lean_ctor_get(v_a_172_, 0);
v_snd_185_ = lean_ctor_get(v_a_172_, 1);
v___x_186_ = l_Lean_ExprStructEq_beq(v_fst_182_, v_fst_184_);
if (v___x_186_ == 0)
{
v___y_179_ = v___x_186_;
goto v___jp_178_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_eq(v_snd_183_, v_snd_185_);
v___y_179_ = v___x_187_;
goto v___jp_178_;
}
v___jp_178_:
{
if (v___y_179_ == 0)
{
v_x_173_ = v_tail_177_;
goto _start;
}
else
{
lean_object* v___x_181_; 
lean_inc(v_value_176_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_value_176_);
return v___x_181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg___boxed(lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(v_a_188_, v_x_189_);
lean_dec(v_x_189_);
lean_dec_ref(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_buckets_193_; lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v_fold_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_buckets_193_ = lean_ctor_get(v_m_191_, 1);
v_fst_194_ = lean_ctor_get(v_a_192_, 0);
v_snd_195_ = lean_ctor_get(v_a_192_, 1);
v___x_196_ = lean_array_get_size(v_buckets_193_);
v___x_197_ = l_Lean_ExprStructEq_hash(v_fst_194_);
v___x_198_ = lean_uint64_of_nat(v_snd_195_);
v___x_199_ = lean_uint64_mix_hash(v___x_197_, v___x_198_);
v___x_200_ = 32ULL;
v___x_201_ = lean_uint64_shift_right(v___x_199_, v___x_200_);
v_fold_202_ = lean_uint64_xor(v___x_199_, v___x_201_);
v___x_203_ = 16ULL;
v___x_204_ = lean_uint64_shift_right(v_fold_202_, v___x_203_);
v___x_205_ = lean_uint64_xor(v_fold_202_, v___x_204_);
v___x_206_ = lean_uint64_to_usize(v___x_205_);
v___x_207_ = lean_usize_of_nat(v___x_196_);
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_sub(v___x_207_, v___x_208_);
v___x_210_ = lean_usize_land(v___x_206_, v___x_209_);
v___x_211_ = lean_array_uget_borrowed(v_buckets_193_, v___x_210_);
v___x_212_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(v_a_192_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg___boxed(lean_object* v_m_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(v_m_213_, v_a_214_);
lean_dec_ref(v_a_214_);
lean_dec_ref(v_m_213_);
return v_res_215_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_220_ = lean_unsigned_to_nat(21u);
v___x_221_ = lean_unsigned_to_nat(69u);
v___x_222_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_224_ = l_mkPanicMessageWithDecl(v___x_223_, v___x_222_, v___x_221_, v___x_220_, v___x_219_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_225_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_226_ = lean_unsigned_to_nat(21u);
v___x_227_ = lean_unsigned_to_nat(70u);
v___x_228_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_229_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_230_ = l_mkPanicMessageWithDecl(v___x_229_, v___x_228_, v___x_227_, v___x_226_, v___x_225_);
return v___x_230_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_231_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_232_ = lean_unsigned_to_nat(21u);
v___x_233_ = lean_unsigned_to_nat(71u);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_235_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_236_ = l_mkPanicMessageWithDecl(v___x_235_, v___x_234_, v___x_233_, v___x_232_, v___x_231_);
return v___x_236_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_238_ = lean_unsigned_to_nat(21u);
v___x_239_ = lean_unsigned_to_nat(68u);
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_242_ = l_mkPanicMessageWithDecl(v___x_241_, v___x_240_, v___x_239_, v___x_238_, v___x_237_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(lean_object* v_start_243_, lean_object* v_stop_244_, lean_object* v_args_245_, lean_object* v_offset_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v___y_249_){
_start:
{
if (lean_obj_tag(v_x_247_) == 5)
{
lean_object* v_fn_250_; lean_object* v_arg_251_; lean_object* v___x_252_; 
v_fn_250_ = lean_ctor_get(v_x_247_, 0);
lean_inc_ref(v_fn_250_);
v_arg_251_ = lean_ctor_get(v_x_247_, 1);
lean_inc_ref(v_arg_251_);
lean_dec_ref(v_x_247_);
v___x_252_ = lean_array_push(v_x_248_, v_arg_251_);
v_x_247_ = v_fn_250_;
v_x_248_ = v___x_252_;
goto _start;
}
else
{
lean_object* v___x_254_; lean_object* v_fst_255_; lean_object* v_snd_256_; size_t v_sz_257_; size_t v___x_258_; lean_object* v___x_259_; lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_275_; 
lean_inc(v_offset_246_);
lean_inc_ref(v_x_247_);
v___x_254_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_243_, v_stop_244_, v_args_245_, v_x_247_, v_offset_246_, v___y_249_);
v_fst_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_fst_255_);
v_snd_256_ = lean_ctor_get(v___x_254_, 1);
lean_inc(v_snd_256_);
lean_dec_ref(v___x_254_);
v_sz_257_ = lean_array_size(v_x_248_);
v___x_258_ = ((size_t)0ULL);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0(v_start_243_, v_stop_244_, v_args_245_, v_offset_246_, v_sz_257_, v___x_258_, v_x_248_, v_snd_256_);
v_fst_260_ = lean_ctor_get(v___x_259_, 0);
v_snd_261_ = lean_ctor_get(v___x_259_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_275_ == 0)
{
v___x_263_ = v___x_259_;
v_isShared_264_ = v_isSharedCheck_275_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_snd_261_);
lean_inc(v_fst_260_);
lean_dec(v___x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_275_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
uint8_t v___x_265_; 
v___x_265_ = l_Lean_Expr_isBVar(v_x_247_);
lean_dec_ref(v_x_247_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = l_Lean_mkAppRev(v_fst_255_, v_fst_260_);
lean_dec(v_fst_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_266_);
v___x_268_ = v___x_263_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_snd_261_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_270_ = 0;
v___x_271_ = l_Lean_Expr_betaRev(v_fst_255_, v_fst_260_, v___x_270_, v___x_270_);
lean_dec(v_fst_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_271_);
v___x_273_ = v___x_263_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_snd_261_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__2));
v___x_277_ = lean_unsigned_to_nat(21u);
v___x_278_ = lean_unsigned_to_nat(72u);
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__1));
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_281_ = l_mkPanicMessageWithDecl(v___x_280_, v___x_279_, v___x_278_, v___x_277_, v___x_276_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(lean_object* v_start_282_, lean_object* v_stop_283_, lean_object* v_args_284_, lean_object* v_e_285_, lean_object* v_offset_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = l_Lean_Expr_looseBVarRange(v_e_285_);
v___x_289_ = lean_nat_dec_le(v___x_288_, v_offset_286_);
lean_dec(v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v_fst_292_; lean_object* v_snd_293_; lean_object* v___y_297_; lean_object* v___x_300_; 
lean_inc(v_offset_286_);
lean_inc_ref(v_e_285_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_e_285_);
lean_ctor_set(v___x_290_, 1, v_offset_286_);
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(v_a_287_, v___x_290_);
if (lean_obj_tag(v___x_300_) == 0)
{
switch(lean_obj_tag(v_e_285_))
{
case 0:
{
lean_object* v_deBruijnIndex_301_; lean_object* v_n_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_deBruijnIndex_301_ = lean_ctor_get(v_e_285_, 0);
lean_inc(v_deBruijnIndex_301_);
lean_dec_ref(v_e_285_);
v_n_302_ = lean_nat_sub(v_stop_283_, v_start_282_);
v___x_303_ = lean_nat_add(v_offset_286_, v_n_302_);
v___x_304_ = lean_nat_dec_lt(v_deBruijnIndex_301_, v___x_303_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_offset_286_);
v___x_305_ = lean_nat_sub(v_deBruijnIndex_301_, v_n_302_);
lean_dec(v_n_302_);
lean_dec(v_deBruijnIndex_301_);
v___x_306_ = l_Lean_mkBVar(v___x_305_);
v_fst_292_ = v___x_306_;
v_snd_293_ = v_a_287_;
goto v___jp_291_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_n_302_);
v___x_307_ = l_Lean_instInhabitedExpr;
v___x_308_ = lean_nat_sub(v_deBruijnIndex_301_, v_offset_286_);
lean_dec(v_deBruijnIndex_301_);
v___x_309_ = lean_nat_sub(v_stop_283_, v___x_308_);
lean_dec(v___x_308_);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_sub(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_array_get_borrowed(v___x_307_, v_args_284_, v___x_311_);
lean_dec(v___x_311_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_expr_lift_loose_bvars(v___x_312_, v___x_313_, v_offset_286_);
lean_dec(v_offset_286_);
v_fst_292_ = v___x_314_;
v_snd_293_ = v_a_287_;
goto v___jp_291_;
}
}
case 1:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref(v_e_285_);
lean_dec(v_offset_286_);
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__3);
v___x_316_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_315_, v_a_287_);
v___y_297_ = v___x_316_;
goto v___jp_296_;
}
case 2:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec_ref(v_e_285_);
lean_dec(v_offset_286_);
v___x_317_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__4);
v___x_318_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_317_, v_a_287_);
v___y_297_ = v___x_318_;
goto v___jp_296_;
}
case 3:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_e_285_);
lean_dec(v_offset_286_);
v___x_319_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__5);
v___x_320_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_319_, v_a_287_);
v___y_297_ = v___x_320_;
goto v___jp_296_;
}
case 4:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_e_285_);
lean_dec(v_offset_286_);
v___x_321_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__6);
v___x_322_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_321_, v_a_287_);
v___y_297_ = v___x_322_;
goto v___jp_296_;
}
case 5:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = l_Lean_Expr_getAppNumArgs(v_e_285_);
v___x_324_ = lean_mk_empty_array_with_capacity(v___x_323_);
lean_dec(v___x_323_);
v___x_325_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_282_, v_stop_283_, v_args_284_, v_offset_286_, v_e_285_, v___x_324_, v_a_287_);
v___y_297_ = v___x_325_;
goto v___jp_296_;
}
case 6:
{
lean_object* v_binderName_326_; lean_object* v_binderType_327_; lean_object* v_body_328_; uint8_t v_binderInfo_329_; lean_object* v___x_330_; lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_fst_336_; lean_object* v_snd_337_; uint8_t v___y_339_; size_t v___x_343_; size_t v___x_344_; uint8_t v___x_345_; 
v_binderName_326_ = lean_ctor_get(v_e_285_, 0);
v_binderType_327_ = lean_ctor_get(v_e_285_, 1);
v_body_328_ = lean_ctor_get(v_e_285_, 2);
v_binderInfo_329_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*3 + 8);
lean_inc(v_offset_286_);
lean_inc_ref(v_binderType_327_);
v___x_330_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_binderType_327_, v_offset_286_, v_a_287_);
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_fst_331_);
v_snd_332_ = lean_ctor_get(v___x_330_, 1);
lean_inc(v_snd_332_);
lean_dec_ref(v___x_330_);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_offset_286_, v___x_333_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_328_);
v___x_335_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_body_328_, v___x_334_, v_snd_332_);
v_fst_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_fst_336_);
v_snd_337_ = lean_ctor_get(v___x_335_, 1);
lean_inc(v_snd_337_);
lean_dec_ref(v___x_335_);
v___x_343_ = lean_ptr_addr(v_binderType_327_);
v___x_344_ = lean_ptr_addr(v_fst_331_);
v___x_345_ = lean_usize_dec_eq(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
v___y_339_ = v___x_345_;
goto v___jp_338_;
}
else
{
size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_ptr_addr(v_body_328_);
v___x_347_ = lean_ptr_addr(v_fst_336_);
v___x_348_ = lean_usize_dec_eq(v___x_346_, v___x_347_);
v___y_339_ = v___x_348_;
goto v___jp_338_;
}
v___jp_338_:
{
if (v___y_339_ == 0)
{
lean_object* v___x_340_; 
lean_inc(v_binderName_326_);
lean_dec_ref(v_e_285_);
v___x_340_ = l_Lean_Expr_lam___override(v_binderName_326_, v_fst_331_, v_fst_336_, v_binderInfo_329_);
v_fst_292_ = v___x_340_;
v_snd_293_ = v_snd_337_;
goto v___jp_291_;
}
else
{
uint8_t v___x_341_; 
v___x_341_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_329_, v_binderInfo_329_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_inc(v_binderName_326_);
lean_dec_ref(v_e_285_);
v___x_342_ = l_Lean_Expr_lam___override(v_binderName_326_, v_fst_331_, v_fst_336_, v_binderInfo_329_);
v_fst_292_ = v___x_342_;
v_snd_293_ = v_snd_337_;
goto v___jp_291_;
}
else
{
lean_dec(v_fst_336_);
lean_dec(v_fst_331_);
v_fst_292_ = v_e_285_;
v_snd_293_ = v_snd_337_;
goto v___jp_291_;
}
}
}
}
case 7:
{
lean_object* v_binderName_349_; lean_object* v_binderType_350_; lean_object* v_body_351_; uint8_t v_binderInfo_352_; lean_object* v___x_353_; lean_object* v_fst_354_; lean_object* v_snd_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_fst_359_; lean_object* v_snd_360_; uint8_t v___y_362_; size_t v___x_366_; size_t v___x_367_; uint8_t v___x_368_; 
v_binderName_349_ = lean_ctor_get(v_e_285_, 0);
v_binderType_350_ = lean_ctor_get(v_e_285_, 1);
v_body_351_ = lean_ctor_get(v_e_285_, 2);
v_binderInfo_352_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*3 + 8);
lean_inc(v_offset_286_);
lean_inc_ref(v_binderType_350_);
v___x_353_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_binderType_350_, v_offset_286_, v_a_287_);
v_fst_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_fst_354_);
v_snd_355_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_snd_355_);
lean_dec_ref(v___x_353_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_offset_286_, v___x_356_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_351_);
v___x_358_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_body_351_, v___x_357_, v_snd_355_);
v_fst_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_fst_359_);
v_snd_360_ = lean_ctor_get(v___x_358_, 1);
lean_inc(v_snd_360_);
lean_dec_ref(v___x_358_);
v___x_366_ = lean_ptr_addr(v_binderType_350_);
v___x_367_ = lean_ptr_addr(v_fst_354_);
v___x_368_ = lean_usize_dec_eq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
v___y_362_ = v___x_368_;
goto v___jp_361_;
}
else
{
size_t v___x_369_; size_t v___x_370_; uint8_t v___x_371_; 
v___x_369_ = lean_ptr_addr(v_body_351_);
v___x_370_ = lean_ptr_addr(v_fst_359_);
v___x_371_ = lean_usize_dec_eq(v___x_369_, v___x_370_);
v___y_362_ = v___x_371_;
goto v___jp_361_;
}
v___jp_361_:
{
if (v___y_362_ == 0)
{
lean_object* v___x_363_; 
lean_inc(v_binderName_349_);
lean_dec_ref(v_e_285_);
v___x_363_ = l_Lean_Expr_forallE___override(v_binderName_349_, v_fst_354_, v_fst_359_, v_binderInfo_352_);
v_fst_292_ = v___x_363_;
v_snd_293_ = v_snd_360_;
goto v___jp_291_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_352_, v_binderInfo_352_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_inc(v_binderName_349_);
lean_dec_ref(v_e_285_);
v___x_365_ = l_Lean_Expr_forallE___override(v_binderName_349_, v_fst_354_, v_fst_359_, v_binderInfo_352_);
v_fst_292_ = v___x_365_;
v_snd_293_ = v_snd_360_;
goto v___jp_291_;
}
else
{
lean_dec(v_fst_359_);
lean_dec(v_fst_354_);
v_fst_292_ = v_e_285_;
v_snd_293_ = v_snd_360_;
goto v___jp_291_;
}
}
}
}
case 8:
{
lean_object* v_declName_372_; lean_object* v_type_373_; lean_object* v_value_374_; lean_object* v_body_375_; uint8_t v_nondep_376_; lean_object* v___x_377_; lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_fst_386_; lean_object* v_snd_387_; uint8_t v___y_389_; size_t v___x_395_; size_t v___x_396_; uint8_t v___x_397_; 
v_declName_372_ = lean_ctor_get(v_e_285_, 0);
v_type_373_ = lean_ctor_get(v_e_285_, 1);
v_value_374_ = lean_ctor_get(v_e_285_, 2);
v_body_375_ = lean_ctor_get(v_e_285_, 3);
v_nondep_376_ = lean_ctor_get_uint8(v_e_285_, sizeof(void*)*4 + 8);
lean_inc(v_offset_286_);
lean_inc_ref(v_type_373_);
v___x_377_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_type_373_, v_offset_286_, v_a_287_);
v_fst_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_fst_378_);
v_snd_379_ = lean_ctor_get(v___x_377_, 1);
lean_inc(v_snd_379_);
lean_dec_ref(v___x_377_);
lean_inc(v_offset_286_);
lean_inc_ref(v_value_374_);
v___x_380_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_value_374_, v_offset_286_, v_snd_379_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v___x_380_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v___x_380_);
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_add(v_offset_286_, v___x_383_);
lean_dec(v_offset_286_);
lean_inc_ref(v_body_375_);
v___x_385_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_body_375_, v___x_384_, v_snd_382_);
v_fst_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_fst_386_);
v_snd_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc(v_snd_387_);
lean_dec_ref(v___x_385_);
v___x_395_ = lean_ptr_addr(v_type_373_);
v___x_396_ = lean_ptr_addr(v_fst_378_);
v___x_397_ = lean_usize_dec_eq(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
v___y_389_ = v___x_397_;
goto v___jp_388_;
}
else
{
size_t v___x_398_; size_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = lean_ptr_addr(v_value_374_);
v___x_399_ = lean_ptr_addr(v_fst_381_);
v___x_400_ = lean_usize_dec_eq(v___x_398_, v___x_399_);
v___y_389_ = v___x_400_;
goto v___jp_388_;
}
v___jp_388_:
{
if (v___y_389_ == 0)
{
lean_object* v___x_390_; 
lean_inc(v_declName_372_);
lean_dec_ref(v_e_285_);
v___x_390_ = l_Lean_Expr_letE___override(v_declName_372_, v_fst_378_, v_fst_381_, v_fst_386_, v_nondep_376_);
v_fst_292_ = v___x_390_;
v_snd_293_ = v_snd_387_;
goto v___jp_291_;
}
else
{
size_t v___x_391_; size_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = lean_ptr_addr(v_body_375_);
v___x_392_ = lean_ptr_addr(v_fst_386_);
v___x_393_ = lean_usize_dec_eq(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_inc(v_declName_372_);
lean_dec_ref(v_e_285_);
v___x_394_ = l_Lean_Expr_letE___override(v_declName_372_, v_fst_378_, v_fst_381_, v_fst_386_, v_nondep_376_);
v_fst_292_ = v___x_394_;
v_snd_293_ = v_snd_387_;
goto v___jp_291_;
}
else
{
lean_dec(v_fst_386_);
lean_dec(v_fst_381_);
lean_dec(v_fst_378_);
v_fst_292_ = v_e_285_;
v_snd_293_ = v_snd_387_;
goto v___jp_291_;
}
}
}
}
case 9:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec_ref(v_e_285_);
lean_dec(v_offset_286_);
v___x_401_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7, &l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7_once, _init_l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__7);
v___x_402_ = l_panic___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__3(v___x_401_, v_a_287_);
v___y_297_ = v___x_402_;
goto v___jp_296_;
}
case 10:
{
lean_object* v_data_403_; lean_object* v_expr_404_; lean_object* v___x_405_; lean_object* v_fst_406_; lean_object* v_snd_407_; size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v_data_403_ = lean_ctor_get(v_e_285_, 0);
v_expr_404_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_expr_404_);
v___x_405_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_expr_404_, v_offset_286_, v_a_287_);
v_fst_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_fst_406_);
v_snd_407_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_snd_407_);
lean_dec_ref(v___x_405_);
v___x_408_ = lean_ptr_addr(v_expr_404_);
v___x_409_ = lean_ptr_addr(v_fst_406_);
v___x_410_ = lean_usize_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_inc(v_data_403_);
lean_dec_ref(v_e_285_);
v___x_411_ = l_Lean_Expr_mdata___override(v_data_403_, v_fst_406_);
v_fst_292_ = v___x_411_;
v_snd_293_ = v_snd_407_;
goto v___jp_291_;
}
else
{
lean_dec(v_fst_406_);
v_fst_292_ = v_e_285_;
v_snd_293_ = v_snd_407_;
goto v___jp_291_;
}
}
default: 
{
lean_object* v_typeName_412_; lean_object* v_idx_413_; lean_object* v_struct_414_; lean_object* v___x_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; size_t v___x_418_; size_t v___x_419_; uint8_t v___x_420_; 
v_typeName_412_ = lean_ctor_get(v_e_285_, 0);
v_idx_413_ = lean_ctor_get(v_e_285_, 1);
v_struct_414_ = lean_ctor_get(v_e_285_, 2);
lean_inc_ref(v_struct_414_);
v___x_415_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_282_, v_stop_283_, v_args_284_, v_struct_414_, v_offset_286_, v_a_287_);
v_fst_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_fst_416_);
v_snd_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_snd_417_);
lean_dec_ref(v___x_415_);
v___x_418_ = lean_ptr_addr(v_struct_414_);
v___x_419_ = lean_ptr_addr(v_fst_416_);
v___x_420_ = lean_usize_dec_eq(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_inc(v_idx_413_);
lean_inc(v_typeName_412_);
lean_dec_ref(v_e_285_);
v___x_421_ = l_Lean_Expr_proj___override(v_typeName_412_, v_idx_413_, v_fst_416_);
v_fst_292_ = v___x_421_;
v_snd_293_ = v_snd_417_;
goto v___jp_291_;
}
else
{
lean_dec(v_fst_416_);
v_fst_292_ = v_e_285_;
v_snd_293_ = v_snd_417_;
goto v___jp_291_;
}
}
}
}
else
{
lean_object* v_val_422_; lean_object* v___x_423_; 
lean_dec_ref(v___x_290_);
lean_dec(v_offset_286_);
lean_dec_ref(v_e_285_);
v_val_422_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_val_422_);
lean_dec_ref(v___x_300_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_val_422_);
lean_ctor_set(v___x_423_, 1, v_a_287_);
return v___x_423_;
}
v___jp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_inc_ref(v_fst_292_);
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(v_snd_293_, v___x_290_, v_fst_292_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_fst_292_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
return v___x_295_;
}
v___jp_296_:
{
lean_object* v_fst_298_; lean_object* v_snd_299_; 
v_fst_298_ = lean_ctor_get(v___y_297_, 0);
lean_inc(v_fst_298_);
v_snd_299_ = lean_ctor_get(v___y_297_, 1);
lean_inc(v_snd_299_);
lean_dec_ref(v___y_297_);
v_fst_292_ = v_fst_298_;
v_snd_293_ = v_snd_299_;
goto v___jp_291_;
}
}
else
{
lean_object* v___x_424_; 
lean_dec(v_offset_286_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_e_285_);
lean_ctor_set(v___x_424_, 1, v_a_287_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0(lean_object* v_start_425_, lean_object* v_stop_426_, lean_object* v_args_427_, lean_object* v_offset_428_, size_t v_sz_429_, size_t v_i_430_, lean_object* v_bs_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = lean_usize_dec_lt(v_i_430_, v_sz_429_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_dec(v_offset_428_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v_bs_431_);
lean_ctor_set(v___x_434_, 1, v___y_432_);
return v___x_434_;
}
else
{
lean_object* v_v_435_; lean_object* v___x_436_; lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___x_439_; lean_object* v_bs_x27_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v_v_435_ = lean_array_uget_borrowed(v_bs_431_, v_i_430_);
lean_inc(v_offset_428_);
lean_inc(v_v_435_);
v___x_436_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_425_, v_stop_426_, v_args_427_, v_v_435_, v_offset_428_, v___y_432_);
v_fst_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_snd_438_);
lean_dec_ref(v___x_436_);
v___x_439_ = lean_unsigned_to_nat(0u);
v_bs_x27_440_ = lean_array_uset(v_bs_431_, v_i_430_, v___x_439_);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_430_, v___x_441_);
v___x_443_ = lean_array_uset(v_bs_x27_440_, v_i_430_, v_fst_437_);
v_i_430_ = v___x_442_;
v_bs_431_ = v___x_443_;
v___y_432_ = v_snd_438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0___boxed(lean_object* v_start_445_, lean_object* v_stop_446_, lean_object* v_args_447_, lean_object* v_offset_448_, lean_object* v_sz_449_, lean_object* v_i_450_, lean_object* v_bs_451_, lean_object* v___y_452_){
_start:
{
size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_sz_boxed_453_ = lean_unbox_usize(v_sz_449_);
lean_dec(v_sz_449_);
v_i_boxed_454_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__0(v_start_445_, v_stop_446_, v_args_447_, v_offset_448_, v_sz_boxed_453_, v_i_boxed_454_, v_bs_451_, v___y_452_);
lean_dec_ref(v_args_447_);
lean_dec(v_stop_446_);
lean_dec(v_start_445_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4___boxed(lean_object* v_start_456_, lean_object* v_stop_457_, lean_object* v_args_458_, lean_object* v_offset_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__4(v_start_456_, v_stop_457_, v_args_458_, v_offset_459_, v_x_460_, v_x_461_, v___y_462_);
lean_dec_ref(v_args_458_);
lean_dec(v_stop_457_);
lean_dec(v_start_456_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* v_start_464_, lean_object* v_stop_465_, lean_object* v_args_466_, lean_object* v_e_467_, lean_object* v_offset_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_464_, v_stop_465_, v_args_466_, v_e_467_, v_offset_468_, v_a_469_);
lean_dec_ref(v_args_466_);
lean_dec(v_stop_465_);
lean_dec(v_start_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1(lean_object* v_00_u03b2_471_, lean_object* v_m_472_, lean_object* v_a_473_, lean_object* v_b_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(v_m_472_, v_a_473_, v_b_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2(lean_object* v_00_u03b2_476_, lean_object* v_m_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(v_m_477_, v_a_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2___boxed(lean_object* v_00_u03b2_480_, lean_object* v_m_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2(v_00_u03b2_480_, v_m_481_, v_a_482_);
lean_dec_ref(v_a_482_);
lean_dec_ref(v_m_481_);
return v_res_483_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1(lean_object* v_00_u03b2_484_, lean_object* v_a_485_, lean_object* v_x_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___redArg(v_a_485_, v_x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_488_, lean_object* v_a_489_, lean_object* v_x_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__1(v_00_u03b2_488_, v_a_489_, v_x_490_);
lean_dec(v_x_490_);
lean_dec_ref(v_a_489_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2(lean_object* v_00_u03b2_493_, lean_object* v_data_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2___redArg(v_data_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3(lean_object* v_00_u03b2_496_, lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v_x_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__3___redArg(v_a_497_, v_b_498_, v_x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5(lean_object* v_00_u03b2_501_, lean_object* v_a_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___redArg(v_a_502_, v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_505_, lean_object* v_a_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__5(v_00_u03b2_505_, v_a_506_, v_x_507_);
lean_dec(v_x_507_);
lean_dec_ref(v_a_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_509_, lean_object* v_i_510_, lean_object* v_source_511_, lean_object* v_target_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4___redArg(v_i_510_, v_source_511_, v_target_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit_spec__1_spec__2_spec__4_spec__7___redArg(v_x_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* v_msg_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = l_Lean_instInhabitedExpr;
v___x_520_ = lean_panic_fn(v___x_519_, v_msg_518_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__2(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__1));
v___x_524_ = lean_unsigned_to_nat(4u);
v___x_525_ = lean_unsigned_to_nat(34u);
v___x_526_ = ((lean_object*)(l_Lean_Expr_instantiateBetaRevRange___closed__0));
v___x_527_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit___closed__0));
v___x_528_ = l_mkPanicMessageWithDecl(v___x_527_, v___x_526_, v___x_525_, v___x_524_, v___x_523_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__3(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_box(0);
v___x_530_ = lean_unsigned_to_nat(16u);
v___x_531_ = lean_mk_array(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__3, &l_Lean_Expr_instantiateBetaRevRange___closed__3_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__3);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* v_e_535_, lean_object* v_start_536_, lean_object* v_stop_537_, lean_object* v_args_538_){
_start:
{
uint8_t v___y_540_; uint8_t v___x_549_; 
v___x_549_ = l_Lean_Expr_hasLooseBVars(v_e_535_);
if (v___x_549_ == 0)
{
v___y_540_ = v___x_549_;
goto v___jp_539_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = lean_nat_dec_lt(v_start_536_, v_stop_537_);
v___y_540_ = v___x_550_;
goto v___jp_539_;
}
v___jp_539_:
{
if (v___y_540_ == 0)
{
return v_e_535_;
}
else
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_array_get_size(v_args_538_);
v___x_542_ = lean_nat_dec_le(v_stop_537_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_e_535_);
v___x_543_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__2, &l_Lean_Expr_instantiateBetaRevRange___closed__2_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__2);
v___x_544_ = l_panic___at___00Lean_Expr_instantiateBetaRevRange_spec__0(v___x_543_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_fst_548_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_obj_once(&l_Lean_Expr_instantiateBetaRevRange___closed__4, &l_Lean_Expr_instantiateBetaRevRange___closed__4_once, _init_l_Lean_Expr_instantiateBetaRevRange___closed__4);
v___x_547_ = l___private_Lean_Meta_InferType_0__Lean_Expr_instantiateBetaRevRange_visit(v_start_536_, v_stop_537_, v_args_538_, v_e_535_, v___x_545_, v___x_546_);
v_fst_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_fst_548_);
lean_dec_ref(v___x_547_);
return v_fst_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* v_e_551_, lean_object* v_start_552_, lean_object* v_stop_553_, lean_object* v_args_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_Expr_instantiateBetaRevRange(v_e_551_, v_start_552_, v_stop_553_, v_args_554_);
lean_dec_ref(v_args_554_);
lean_dec(v_stop_553_);
lean_dec(v_start_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* v_msgData_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_env_563_; lean_object* v___x_564_; lean_object* v_mctx_565_; lean_object* v_lctx_566_; lean_object* v_options_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_562_ = lean_st_ref_get(v___y_560_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_563_);
lean_dec(v___x_562_);
v___x_564_ = lean_st_ref_get(v___y_558_);
v_mctx_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_mctx_565_);
lean_dec(v___x_564_);
v_lctx_566_ = lean_ctor_get(v___y_557_, 2);
v_options_567_ = lean_ctor_get(v___y_559_, 2);
lean_inc_ref(v_options_567_);
lean_inc_ref(v_lctx_566_);
v___x_568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_568_, 0, v_env_563_);
lean_ctor_set(v___x_568_, 1, v_mctx_565_);
lean_ctor_set(v___x_568_, 2, v_lctx_566_);
lean_ctor_set(v___x_568_, 3, v_options_567_);
v___x_569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_msgData_556_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* v_msgData_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msgData_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_ref_584_; lean_object* v___x_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v_ref_584_ = lean_ctor_get(v___y_581_, 5);
v___x_585_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0_spec__0(v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_inc(v_ref_584_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_ref_584_);
lean_ctor_set(v___x_590_, 1, v_a_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_601_;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l_Lean_Meta_throwFunctionExpected___redArg___closed__0));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* v_f_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_obj_once(&l_Lean_Meta_throwFunctionExpected___redArg___closed__1, &l_Lean_Meta_throwFunctionExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
v___x_612_ = l_Lean_indentExpr(v_f_605_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_613_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* v_f_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* v_00_u03b1_622_, lean_object* v_f_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_throwFunctionExpected___redArg(v_f_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* v_00_u03b1_630_, lean_object* v_f_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Meta_throwFunctionExpected(v_00_u03b1_630_, v_f_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(lean_object* v_00_u03b1_638_, lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* v_00_u03b1_646_, lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0(v_00_u03b1_646_, v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* v_upperBound_654_, lean_object* v_args_655_, lean_object* v_f_656_, lean_object* v_a_657_, lean_object* v_b_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_a_665_; uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_lt(v_a_657_, v_upperBound_654_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_a_657_);
lean_dec_ref(v_f_656_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_b_658_);
return v___x_670_;
}
else
{
lean_object* v_fst_671_; 
v_fst_671_ = lean_ctor_get(v_b_658_, 0);
lean_inc(v_fst_671_);
if (lean_obj_tag(v_fst_671_) == 7)
{
lean_object* v_snd_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
v_snd_672_ = lean_ctor_get(v_b_658_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_b_658_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v_b_658_, 0);
lean_dec(v_unused_681_);
v___x_674_ = v_b_658_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snd_672_);
lean_dec(v_b_658_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_body_676_; lean_object* v___x_678_; 
v_body_676_ = lean_ctor_get(v_fst_671_, 2);
lean_inc_ref(v_body_676_);
lean_dec_ref(v_fst_671_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v_body_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_body_676_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_snd_672_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
v_a_665_ = v___x_678_;
goto v___jp_664_;
}
}
}
else
{
lean_object* v_snd_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_717_; 
v_snd_682_ = lean_ctor_get(v_b_658_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_b_658_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v_b_658_, 0);
lean_dec(v_unused_718_);
v___x_684_ = v_b_658_;
v_isShared_685_ = v_isSharedCheck_717_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snd_682_);
lean_dec(v_b_658_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_717_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc(v_fst_671_);
v___x_686_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_671_, v_snd_682_, v_a_657_, v_args_655_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_687_ = lean_whnf(v___x_686_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref(v___x_687_);
if (lean_obj_tag(v_a_688_) == 7)
{
lean_object* v_body_689_; lean_object* v___x_691_; 
lean_dec(v_snd_682_);
lean_dec(v_fst_671_);
v_body_689_ = lean_ctor_get(v_a_688_, 2);
lean_inc_ref(v_body_689_);
lean_dec_ref(v_a_688_);
lean_inc(v_a_657_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_a_657_);
lean_ctor_set(v___x_684_, 0, v_body_689_);
v___x_691_ = v___x_684_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_body_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_a_657_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_a_665_ = v___x_691_;
goto v___jp_664_;
}
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec(v_a_688_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_a_657_, v___x_694_);
lean_inc_ref(v_f_656_);
v___x_696_ = l_Lean_mkAppRange(v_f_656_, v___x_693_, v___x_695_, v_args_655_);
lean_dec(v___x_695_);
v___x_697_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_696_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_699_; 
lean_dec_ref(v___x_697_);
if (v_isShared_685_ == 0)
{
v___x_699_ = v___x_684_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fst_671_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_snd_682_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_a_665_ = v___x_699_;
goto v___jp_664_;
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_684_);
lean_dec(v_snd_682_);
lean_dec(v_fst_671_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_a_657_);
lean_dec_ref(v_f_656_);
v_a_701_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_697_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_697_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_del_object(v___x_684_);
lean_dec(v_snd_682_);
lean_dec(v_fst_671_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_a_657_);
lean_dec_ref(v_f_656_);
v_a_709_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_687_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_687_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
v___jp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v_a_657_, v___x_666_);
lean_dec(v_a_657_);
v_a_657_ = v___x_667_;
v_b_658_ = v_a_665_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* v_upperBound_719_, lean_object* v_args_720_, lean_object* v_f_721_, lean_object* v_a_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_719_, v_args_720_, v_f_721_, v_a_722_, v_b_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
lean_dec_ref(v_args_720_);
lean_dec(v_upperBound_719_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* v_f_730_, lean_object* v_args_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; 
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc_ref(v_f_730_);
v___x_737_ = lean_infer_type(v_f_730_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref(v___x_737_);
v___x_739_ = lean_array_get_size(v_args_731_);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_738_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v___x_739_, v_args_731_, v_f_730_, v___x_740_, v___x_741_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_753_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_fst_747_; lean_object* v_snd_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v_fst_747_ = lean_ctor_get(v_a_743_, 0);
lean_inc(v_fst_747_);
v_snd_748_ = lean_ctor_get(v_a_743_, 1);
lean_inc(v_snd_748_);
lean_dec(v_a_743_);
v___x_749_ = l_Lean_Expr_instantiateBetaRevRange(v_fst_747_, v_snd_748_, v___x_739_, v_args_731_);
lean_dec(v_snd_748_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_a_754_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_742_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_742_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec_ref(v_f_730_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* v_f_762_, lean_object* v_args_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v_f_762_, v_args_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec_ref(v_args_763_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* v_upperBound_770_, lean_object* v_args_771_, lean_object* v_f_772_, lean_object* v_inst_773_, lean_object* v_R_774_, lean_object* v_a_775_, lean_object* v_b_776_, lean_object* v_c_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(v_upperBound_770_, v_args_771_, v_f_772_, v_a_775_, v_b_776_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* v_upperBound_784_, lean_object* v_args_785_, lean_object* v_f_786_, lean_object* v_inst_787_, lean_object* v_R_788_, lean_object* v_a_789_, lean_object* v_b_790_, lean_object* v_c_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(v_upperBound_784_, v_args_785_, v_f_786_, v_inst_787_, v_R_788_, v_a_789_, v_b_790_, v_c_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec_ref(v_args_785_);
lean_dec(v_upperBound_784_);
return v_res_797_;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* v_constName_801_, lean_object* v_us_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = lean_obj_once(&l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1, &l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1_once, _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
v___x_809_ = l_Lean_mkConst(v_constName_801_, v_us_802_);
v___x_810_ = l_Lean_MessageData_ofExpr(v___x_809_);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_808_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_811_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* v_constName_813_, lean_object* v_us_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_813_, v_us_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* v_00_u03b1_821_, lean_object* v_constName_822_, lean_object* v_us_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_constName_822_, v_us_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* v_00_u03b1_830_, lean_object* v_constName_831_, lean_object* v_us_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Meta_throwIncorrectNumberOfLevels(v_00_u03b1_830_, v_constName_831_, v_us_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_839_, lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_fileName_846_; lean_object* v_fileMap_847_; lean_object* v_options_848_; lean_object* v_currRecDepth_849_; lean_object* v_maxRecDepth_850_; lean_object* v_ref_851_; lean_object* v_currNamespace_852_; lean_object* v_openDecls_853_; lean_object* v_initHeartbeats_854_; lean_object* v_maxHeartbeats_855_; lean_object* v_quotContext_856_; lean_object* v_currMacroScope_857_; uint8_t v_diag_858_; lean_object* v_cancelTk_x3f_859_; uint8_t v_suppressElabErrors_860_; lean_object* v_inheritedTraceOptions_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_870_; 
v_fileName_846_ = lean_ctor_get(v___y_843_, 0);
v_fileMap_847_ = lean_ctor_get(v___y_843_, 1);
v_options_848_ = lean_ctor_get(v___y_843_, 2);
v_currRecDepth_849_ = lean_ctor_get(v___y_843_, 3);
v_maxRecDepth_850_ = lean_ctor_get(v___y_843_, 4);
v_ref_851_ = lean_ctor_get(v___y_843_, 5);
v_currNamespace_852_ = lean_ctor_get(v___y_843_, 6);
v_openDecls_853_ = lean_ctor_get(v___y_843_, 7);
v_initHeartbeats_854_ = lean_ctor_get(v___y_843_, 8);
v_maxHeartbeats_855_ = lean_ctor_get(v___y_843_, 9);
v_quotContext_856_ = lean_ctor_get(v___y_843_, 10);
v_currMacroScope_857_ = lean_ctor_get(v___y_843_, 11);
v_diag_858_ = lean_ctor_get_uint8(v___y_843_, sizeof(void*)*14);
v_cancelTk_x3f_859_ = lean_ctor_get(v___y_843_, 12);
v_suppressElabErrors_860_ = lean_ctor_get_uint8(v___y_843_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_861_ = lean_ctor_get(v___y_843_, 13);
v_isSharedCheck_870_ = !lean_is_exclusive(v___y_843_);
if (v_isSharedCheck_870_ == 0)
{
v___x_863_ = v___y_843_;
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_inheritedTraceOptions_861_);
lean_inc(v_cancelTk_x3f_859_);
lean_inc(v_currMacroScope_857_);
lean_inc(v_quotContext_856_);
lean_inc(v_maxHeartbeats_855_);
lean_inc(v_initHeartbeats_854_);
lean_inc(v_openDecls_853_);
lean_inc(v_currNamespace_852_);
lean_inc(v_ref_851_);
lean_inc(v_maxRecDepth_850_);
lean_inc(v_currRecDepth_849_);
lean_inc(v_options_848_);
lean_inc(v_fileMap_847_);
lean_inc(v_fileName_846_);
lean_dec(v___y_843_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_ref_865_; lean_object* v___x_867_; 
v_ref_865_ = l_Lean_replaceRef(v_ref_839_, v_ref_851_);
lean_dec(v_ref_851_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 5, v_ref_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_fileName_846_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_fileMap_847_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_options_848_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_currRecDepth_849_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_maxRecDepth_850_);
lean_ctor_set(v_reuseFailAlloc_869_, 5, v_ref_865_);
lean_ctor_set(v_reuseFailAlloc_869_, 6, v_currNamespace_852_);
lean_ctor_set(v_reuseFailAlloc_869_, 7, v_openDecls_853_);
lean_ctor_set(v_reuseFailAlloc_869_, 8, v_initHeartbeats_854_);
lean_ctor_set(v_reuseFailAlloc_869_, 9, v_maxHeartbeats_855_);
lean_ctor_set(v_reuseFailAlloc_869_, 10, v_quotContext_856_);
lean_ctor_set(v_reuseFailAlloc_869_, 11, v_currMacroScope_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 12, v_cancelTk_x3f_859_);
lean_ctor_set(v_reuseFailAlloc_869_, 13, v_inheritedTraceOptions_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, sizeof(void*)*14, v_diag_858_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, sizeof(void*)*14 + 1, v_suppressElabErrors_860_);
v___x_867_ = v_reuseFailAlloc_869_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v_msg_840_, v___y_841_, v___y_842_, v___x_867_, v___y_844_);
lean_dec_ref(v___x_867_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_871_, lean_object* v_msg_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_871_, v_msg_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v_ref_871_);
return v_res_878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_879_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
lean_ctor_set(v___x_884_, 3, v___x_882_);
lean_ctor_set(v___x_884_, 4, v___x_882_);
lean_ctor_set(v___x_884_, 5, v___x_882_);
lean_ctor_set(v___x_884_, 6, v___x_882_);
lean_ctor_set(v___x_884_, 7, v___x_882_);
lean_ctor_set(v___x_884_, 8, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(32u);
v___x_886_ = lean_mk_empty_array_with_capacity(v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_888_ = ((size_t)5ULL);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_unsigned_to_nat(32u);
v___x_891_ = lean_mk_empty_array_with_capacity(v___x_890_);
v___x_892_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_893_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___x_891_);
lean_ctor_set(v___x_893_, 2, v___x_889_);
lean_ctor_set(v___x_893_, 3, v___x_889_);
lean_ctor_set_usize(v___x_893_, 4, v___x_888_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = lean_box(1);
v___x_895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_896_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
lean_ctor_set(v___x_897_, 2, v___x_894_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_919_, lean_object* v_declHint_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; lean_object* v_env_924_; uint8_t v___x_925_; 
v___x_923_ = lean_st_ref_get(v___y_921_);
v_env_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc_ref(v_env_924_);
lean_dec(v___x_923_);
v___x_925_ = l_Lean_Name_isAnonymous(v_declHint_920_);
if (v___x_925_ == 0)
{
uint8_t v_isExporting_926_; 
v_isExporting_926_ = lean_ctor_get_uint8(v_env_924_, sizeof(void*)*8);
if (v_isExporting_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec_ref(v_env_924_);
lean_dec(v_declHint_920_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_msg_919_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; uint8_t v___x_929_; 
lean_inc_ref(v_env_924_);
v___x_928_ = l_Lean_Environment_setExporting(v_env_924_, v___x_925_);
lean_inc(v_declHint_920_);
lean_inc_ref(v___x_928_);
v___x_929_ = l_Lean_Environment_contains(v___x_928_, v_declHint_920_, v_isExporting_926_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v___x_928_);
lean_dec_ref(v_env_924_);
lean_dec(v_declHint_920_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_msg_919_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_c_936_; lean_object* v___x_937_; 
v___x_931_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_933_ = l_Lean_Options_empty;
v___x_934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_934_, 0, v___x_928_);
lean_ctor_set(v___x_934_, 1, v___x_931_);
lean_ctor_set(v___x_934_, 2, v___x_932_);
lean_ctor_set(v___x_934_, 3, v___x_933_);
lean_inc(v_declHint_920_);
v___x_935_ = l_Lean_MessageData_ofConstName(v_declHint_920_, v___x_925_);
v_c_936_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_936_, 0, v___x_934_);
lean_ctor_set(v_c_936_, 1, v___x_935_);
v___x_937_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_924_, v_declHint_920_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec_ref(v_env_924_);
lean_dec(v_declHint_920_);
v___x_938_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_c_936_);
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_MessageData_note(v___x_941_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v_msg_919_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
else
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_980_; 
v_val_945_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_980_ == 0)
{
v___x_947_ = v___x_937_;
v_isShared_948_ = v_isSharedCheck_980_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v___x_937_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_980_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_mod_952_; uint8_t v___x_953_; 
v___x_949_ = lean_box(0);
v___x_950_ = l_Lean_Environment_header(v_env_924_);
lean_dec_ref(v_env_924_);
v___x_951_ = l_Lean_EnvironmentHeader_moduleNames(v___x_950_);
v_mod_952_ = lean_array_get(v___x_949_, v___x_951_, v_val_945_);
lean_dec(v_val_945_);
lean_dec_ref(v___x_951_);
v___x_953_ = l_Lean_isPrivateName(v_declHint_920_);
lean_dec(v_declHint_920_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_954_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_c_936_);
v___x_956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_MessageData_ofName(v_mod_952_);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = l_Lean_MessageData_note(v___x_961_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v_msg_919_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 0);
lean_ctor_set(v___x_947_, 0, v___x_963_);
v___x_965_ = v___x_947_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_967_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_c_936_);
v___x_969_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_MessageData_ofName(v_mod_952_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_MessageData_note(v___x_974_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v_msg_919_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 0);
lean_ctor_set(v___x_947_, 0, v___x_976_);
v___x_978_ = v___x_947_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_981_; 
lean_dec_ref(v_env_924_);
lean_dec(v_declHint_920_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_msg_919_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_982_, lean_object* v_declHint_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_982_, v_declHint_983_, v___y_984_);
lean_dec(v___y_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_987_, lean_object* v_declHint_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1004_; 
v___x_994_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_987_, v_declHint_988_, v___y_992_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_999_ = l_Lean_unknownIdentifierMessageTag;
v___x_1000_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v_a_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_1005_, lean_object* v_declHint_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1005_, v_declHint_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1013_, lean_object* v_msg_1014_, lean_object* v_declHint_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1023_; 
v___x_1021_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1014_, v_declHint_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1013_, v_a_1022_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1024_, lean_object* v_msg_1025_, lean_object* v_declHint_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1024_, v_msg_1025_, v_declHint_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v_ref_1024_);
return v_res_1032_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1039_, lean_object* v_constName_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1046_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1047_ = 0;
lean_inc(v_constName_1040_);
v___x_1048_ = l_Lean_MessageData_ofConstName(v_constName_1040_, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1046_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1039_, v___x_1051_, v_constName_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1053_, lean_object* v_constName_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1053_, v_constName_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v_ref_1053_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* v_constName_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_ref_1067_; lean_object* v___x_1068_; 
v_ref_1067_ = lean_ctor_get(v___y_1064_, 5);
lean_inc(v_ref_1067_);
v___x_1068_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1067_, v_constName_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v_ref_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* v_constName_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; lean_object* v_env_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = lean_st_ref_get(v___y_1080_);
v_env_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_env_1083_);
lean_dec(v___x_1082_);
v___x_1084_ = 0;
lean_inc(v_constName_1076_);
v___x_1085_ = l_Lean_Environment_findConstVal_x3f(v_env_1083_, v_constName_1076_, v___x_1084_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1086_;
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v___y_1079_);
lean_dec(v_constName_1076_);
v_val_1087_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 0);
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_val_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* v_constName_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_constName_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* v_c_1102_, lean_object* v_us_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v___x_1109_; 
lean_inc_ref(v_a_1106_);
lean_inc(v_c_1102_);
v___x_1109_ = l_Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(v_c_1102_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v_levelParams_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v___x_1109_);
v_levelParams_1111_ = lean_ctor_get(v_a_1110_, 1);
v___x_1112_ = l_List_lengthTR___redArg(v_levelParams_1111_);
v___x_1113_ = l_List_lengthTR___redArg(v_us_1103_);
v___x_1114_ = lean_nat_dec_eq(v___x_1112_, v___x_1113_);
lean_dec(v___x_1113_);
lean_dec(v___x_1112_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec(v_a_1110_);
v___x_1115_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_c_1102_, v_us_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec_ref(v_a_1106_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
lean_dec_ref(v_a_1106_);
lean_dec(v_c_1102_);
v___x_1116_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1110_, v_us_1103_, v_a_1107_);
return v___x_1116_;
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v_a_1106_);
lean_dec(v_us_1103_);
lean_dec(v_c_1102_);
v_a_1117_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1109_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1109_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* v_c_1125_, lean_object* v_us_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_c_1125_, v_us_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* v_00_u03b1_1133_, lean_object* v_constName_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_constName_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(v_00_u03b1_1141_, v_constName_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1149_, lean_object* v_ref_1150_, lean_object* v_constName_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___redArg(v_ref_1150_, v_constName_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_ref_1159_, lean_object* v_constName_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1(v_00_u03b1_1158_, v_ref_1159_, v_constName_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_ref_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1167_, lean_object* v_ref_1168_, lean_object* v_msg_1169_, lean_object* v_declHint_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1168_, v_msg_1169_, v_declHint_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_ref_1178_, lean_object* v_msg_1179_, lean_object* v_declHint_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1177_, v_ref_1178_, v_msg_1179_, v_declHint_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v_ref_1178_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1187_, lean_object* v_declHint_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1187_, v_declHint_1188_, v___y_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1195_, lean_object* v_declHint_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1195_, v_declHint_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1203_, lean_object* v_ref_1204_, lean_object* v_msg_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1204_, v_msg_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1212_, lean_object* v_ref_1213_, lean_object* v_msg_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1212_, v_ref_1213_, v_msg_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_ref_1213_);
return v_res_1220_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2));
v___x_1226_ = l_Lean_stringToMessageData(v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* v_structName_1227_, lean_object* v_idx_1228_, lean_object* v_e_1229_, lean_object* v_a_1230_, lean_object* v_00_u03b1_1231_, lean_object* v_x_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1238_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
v___x_1239_ = l_Lean_mkProj(v_structName_1227_, v_idx_1228_, v_e_1229_);
v___x_1240_ = l_Lean_indentExpr(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_indentExpr(v_a_1230_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1245_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* v_structName_1247_, lean_object* v_idx_1248_, lean_object* v_e_1249_, lean_object* v_a_1250_, lean_object* v_00_u03b1_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1247_, v_idx_1248_, v_e_1249_, v_a_1250_, v_00_u03b1_1251_, v_x_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* v_constName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; lean_object* v_env_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1265_ = lean_st_ref_get(v___y_1263_);
v_env_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc_ref(v_env_1266_);
lean_dec(v___x_1265_);
v___x_1267_ = 0;
lean_inc(v_constName_1259_);
v___x_1268_ = l_Lean_Environment_find_x3f(v_env_1266_, v_constName_1259_, v___x_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(v_constName_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v___x_1269_;
}
else
{
lean_object* v_val_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v___y_1262_);
lean_dec(v_constName_1259_);
v_val_1270_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1268_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_val_1270_);
lean_dec(v___x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set_tag(v___x_1272_, 0);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_val_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* v_constName_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_constName_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(lean_object* v_upperBound_1285_, lean_object* v_structName_1286_, lean_object* v_e_1287_, lean_object* v_idx_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_b_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_a_1298_; uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_lt(v_a_1290_, v_upperBound_1285_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_idx_1288_);
lean_dec_ref(v_e_1287_);
lean_dec(v_structName_1286_);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_b_1291_);
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; 
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
lean_inc(v___y_1293_);
lean_inc_ref(v___y_1292_);
v___x_1304_ = lean_whnf(v_b_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1304_);
if (lean_obj_tag(v_a_1305_) == 7)
{
lean_object* v_body_1306_; uint8_t v___x_1307_; 
v_body_1306_ = lean_ctor_get(v_a_1305_, 2);
lean_inc_ref(v_body_1306_);
lean_dec_ref(v_a_1305_);
v___x_1307_ = l_Lean_Expr_hasLooseBVars(v_body_1306_);
if (v___x_1307_ == 0)
{
v_a_1298_ = v_body_1306_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_inc_ref(v_e_1287_);
lean_inc(v_a_1290_);
lean_inc(v_structName_1286_);
v___x_1308_ = l_Lean_mkProj(v_structName_1286_, v_a_1290_, v_e_1287_);
v___x_1309_ = lean_expr_instantiate1(v_body_1306_, v___x_1308_);
lean_dec_ref(v___x_1308_);
lean_dec_ref(v_body_1306_);
v_a_1298_ = v___x_1309_;
goto v___jp_1297_;
}
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1310_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1287_);
lean_inc(v_idx_1288_);
lean_inc(v_structName_1286_);
v___x_1311_ = l_Lean_mkProj(v_structName_1286_, v_idx_1288_, v_e_1287_);
v___x_1312_ = l_Lean_indentExpr(v___x_1311_);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1310_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_inc_ref(v_a_1289_);
v___x_1316_ = l_Lean_indentExpr(v_a_1289_);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1317_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_dec_ref(v___x_1318_);
v_a_1298_ = v_a_1305_;
goto v___jp_1297_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1305_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_idx_1288_);
lean_dec_ref(v_e_1287_);
lean_dec(v_structName_1286_);
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
else
{
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_idx_1288_);
lean_dec_ref(v_e_1287_);
lean_dec(v_structName_1286_);
return v___x_1304_;
}
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_add(v_a_1290_, v___x_1299_);
lean_dec(v_a_1290_);
v_a_1290_ = v___x_1300_;
v_b_1291_ = v_a_1298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg___boxed(lean_object* v_upperBound_1327_, lean_object* v_structName_1328_, lean_object* v_e_1329_, lean_object* v_idx_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1327_, v_structName_1328_, v_e_1329_, v_idx_1330_, v_a_1331_, v_a_1332_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v_upperBound_1327_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* v_upperBound_1340_, lean_object* v_structName_1341_, lean_object* v_e_1342_, lean_object* v_idx_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_a_1353_; uint8_t v___x_1357_; 
v___x_1357_ = lean_nat_dec_lt(v_a_1345_, v_upperBound_1340_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_idx_1343_);
lean_dec_ref(v_e_1342_);
lean_dec(v_structName_1341_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1346_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; 
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v___y_1348_);
lean_inc_ref(v___y_1347_);
v___x_1359_ = lean_whnf(v_b_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
if (lean_obj_tag(v_a_1360_) == 7)
{
lean_object* v_body_1361_; uint8_t v___x_1362_; 
v_body_1361_ = lean_ctor_get(v_a_1360_, 2);
lean_inc_ref(v_body_1361_);
lean_dec_ref(v_a_1360_);
v___x_1362_ = l_Lean_Expr_hasLooseBVars(v_body_1361_);
if (v___x_1362_ == 0)
{
v_a_1353_ = v_body_1361_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref(v_e_1342_);
lean_inc(v_a_1345_);
lean_inc(v_structName_1341_);
v___x_1363_ = l_Lean_mkProj(v_structName_1341_, v_a_1345_, v_e_1342_);
v___x_1364_ = lean_expr_instantiate1(v_body_1361_, v___x_1363_);
lean_dec_ref(v___x_1363_);
lean_dec_ref(v_body_1361_);
v_a_1353_ = v___x_1364_;
goto v___jp_1352_;
}
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
lean_inc_ref(v_e_1342_);
lean_inc(v_idx_1343_);
lean_inc(v_structName_1341_);
v___x_1366_ = l_Lean_mkProj(v_structName_1341_, v_idx_1343_, v_e_1342_);
v___x_1367_ = l_Lean_indentExpr(v___x_1366_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1365_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
lean_inc_ref(v_a_1344_);
v___x_1371_ = l_Lean_indentExpr(v_a_1344_);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1372_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_dec_ref(v___x_1373_);
v_a_1353_ = v_a_1360_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1360_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_idx_1343_);
lean_dec_ref(v_e_1342_);
lean_dec(v_structName_1341_);
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
else
{
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_idx_1343_);
lean_dec_ref(v_e_1342_);
lean_dec(v_structName_1341_);
return v___x_1359_;
}
}
v___jp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_nat_add(v_a_1345_, v___x_1354_);
lean_dec(v_a_1345_);
v___x_1356_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1340_, v_structName_1341_, v_e_1342_, v_idx_1343_, v_a_1344_, v___x_1355_, v_a_1353_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg___boxed(lean_object* v_upperBound_1382_, lean_object* v_structName_1383_, lean_object* v_e_1384_, lean_object* v_idx_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1382_, v_structName_1383_, v_e_1384_, v_idx_1385_, v_a_1386_, v_a_1387_, v_b_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v_upperBound_1382_);
return v_res_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0(void){
_start:
{
lean_object* v___x_1395_; lean_object* v_dummy_1396_; 
v___x_1395_ = lean_box(0);
v_dummy_1396_ = l_Lean_Expr_sort___override(v___x_1395_);
return v_dummy_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* v_structName_1397_, lean_object* v_idx_1398_, lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1405_; 
lean_inc(v_a_1403_);
lean_inc_ref(v_a_1402_);
lean_inc(v_a_1401_);
lean_inc_ref(v_a_1400_);
lean_inc_ref(v_e_1399_);
v___x_1405_ = lean_infer_type(v_e_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref(v___x_1405_);
lean_inc(v_a_1403_);
lean_inc_ref(v_a_1402_);
lean_inc(v_a_1401_);
lean_inc_ref(v_a_1400_);
v___x_1407_ = lean_whnf(v_a_1406_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = l_Lean_Expr_getAppFn(v_a_1408_);
if (lean_obj_tag(v___x_1409_) == 4)
{
lean_object* v_declName_1410_; lean_object* v_us_1411_; lean_object* v___x_1412_; lean_object* v_env_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v_declName_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_declName_1410_);
v_us_1411_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_us_1411_);
lean_dec_ref(v___x_1409_);
v___x_1412_ = lean_st_ref_get(v_a_1403_);
v_env_1416_ = lean_ctor_get(v___x_1412_, 0);
lean_inc_ref(v_env_1416_);
lean_dec(v___x_1412_);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_Environment_find_x3f(v_env_1416_, v_declName_1410_, v___x_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec(v_us_1411_);
v___x_1419_ = lean_box(0);
v___x_1420_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1419_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v___x_1420_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1421_);
lean_dec_ref(v___x_1418_);
if (lean_obj_tag(v_val_1421_) == 5)
{
lean_object* v_val_1422_; lean_object* v_ctors_1423_; 
v_val_1422_ = lean_ctor_get(v_val_1421_, 0);
lean_inc_ref(v_val_1422_);
lean_dec_ref(v_val_1421_);
v_ctors_1423_ = lean_ctor_get(v_val_1422_, 4);
lean_inc(v_ctors_1423_);
if (lean_obj_tag(v_ctors_1423_) == 1)
{
lean_object* v_tail_1424_; 
v_tail_1424_ = lean_ctor_get(v_ctors_1423_, 1);
if (lean_obj_tag(v_tail_1424_) == 0)
{
lean_object* v_toConstantVal_1425_; lean_object* v_numParams_1426_; lean_object* v_numIndices_1427_; lean_object* v_head_1428_; lean_object* v___x_1429_; 
v_toConstantVal_1425_ = lean_ctor_get(v_val_1422_, 0);
lean_inc_ref(v_toConstantVal_1425_);
v_numParams_1426_ = lean_ctor_get(v_val_1422_, 1);
lean_inc(v_numParams_1426_);
v_numIndices_1427_ = lean_ctor_get(v_val_1422_, 2);
lean_inc(v_numIndices_1427_);
lean_dec_ref(v_val_1422_);
v_head_1428_ = lean_ctor_get(v_ctors_1423_, 0);
lean_inc(v_head_1428_);
lean_dec_ref(v_ctors_1423_);
lean_inc_ref(v_a_1402_);
v___x_1429_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(v_head_1428_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___x_1429_);
if (lean_obj_tag(v_a_1430_) == 6)
{
lean_object* v_val_1431_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v_name_1471_; uint8_t v___x_1472_; 
v_val_1431_ = lean_ctor_get(v_a_1430_, 0);
lean_inc_ref(v_val_1431_);
lean_dec_ref(v_a_1430_);
v_name_1471_ = lean_ctor_get(v_toConstantVal_1425_, 0);
lean_inc(v_name_1471_);
lean_dec_ref(v_toConstantVal_1425_);
v___x_1472_ = lean_name_eq(v_name_1471_, v_structName_1397_);
lean_dec(v_name_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v_val_1431_);
lean_dec(v_numIndices_1427_);
lean_dec(v_numParams_1426_);
lean_dec(v_us_1411_);
v___x_1473_ = lean_box(0);
v___x_1474_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1473_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
v___y_1433_ = v_a_1400_;
v___y_1434_ = v_a_1401_;
v___y_1435_ = v_a_1402_;
v___y_1436_ = v_a_1403_;
goto v___jp_1432_;
}
v___jp_1432_:
{
lean_object* v_dummy_1437_; lean_object* v_nargs_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_dummy_1437_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
v_nargs_1438_ = l_Lean_Expr_getAppNumArgs(v_a_1408_);
lean_inc(v_nargs_1438_);
v___x_1439_ = lean_mk_array(v_nargs_1438_, v_dummy_1437_);
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_sub(v_nargs_1438_, v___x_1440_);
lean_dec(v_nargs_1438_);
lean_inc(v_a_1408_);
v___x_1442_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1408_, v___x_1439_, v___x_1441_);
v___x_1443_ = lean_nat_add(v_numParams_1426_, v_numIndices_1427_);
lean_dec(v_numIndices_1427_);
v___x_1444_ = lean_array_get_size(v___x_1442_);
v___x_1445_ = lean_nat_dec_eq(v___x_1443_, v___x_1444_);
lean_dec(v___x_1443_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v___x_1442_);
lean_dec_ref(v_val_1431_);
lean_dec(v_numParams_1426_);
lean_dec(v_us_1411_);
v___x_1446_ = lean_box(0);
v___x_1447_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1446_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v___x_1447_;
}
else
{
lean_object* v_toConstantVal_1448_; lean_object* v_name_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_toConstantVal_1448_ = lean_ctor_get(v_val_1431_, 0);
lean_inc_ref(v_toConstantVal_1448_);
lean_dec_ref(v_val_1431_);
v_name_1449_ = lean_ctor_get(v_toConstantVal_1448_, 0);
lean_inc(v_name_1449_);
lean_dec_ref(v_toConstantVal_1448_);
v___x_1450_ = l_Lean_mkConst(v_name_1449_, v_us_1411_);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = l_Array_toSubarray___redArg(v___x_1442_, v___x_1451_, v_numParams_1426_);
v___x_1453_ = l_Subarray_copy___redArg(v___x_1452_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
v___x_1454_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_1450_, v___x_1453_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec_ref(v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v_a_1408_);
lean_inc_ref(v_e_1399_);
lean_inc(v_structName_1397_);
lean_inc(v_idx_1398_);
v___x_1456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_idx_1398_, v_structName_1397_, v_e_1399_, v_idx_1398_, v_a_1408_, v___x_1451_, v_a_1455_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
v___x_1458_ = lean_whnf(v_a_1457_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1470_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1470_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1470_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
if (lean_obj_tag(v_a_1459_) == 7)
{
lean_object* v_binderType_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_a_1408_);
lean_dec_ref(v_e_1399_);
lean_dec(v_idx_1398_);
lean_dec(v_structName_1397_);
v_binderType_1463_ = lean_ctor_get(v_a_1459_, 1);
lean_inc_ref(v_binderType_1463_);
lean_dec_ref(v_a_1459_);
v___x_1464_ = lean_expr_consume_type_annotations(v_binderType_1463_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1464_);
v___x_1466_ = v___x_1461_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_del_object(v___x_1461_);
lean_dec(v_a_1459_);
v___x_1468_ = lean_box(0);
v___x_1469_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1468_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v___x_1469_;
}
}
}
else
{
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_a_1408_);
lean_dec_ref(v_e_1399_);
lean_dec(v_idx_1398_);
lean_dec(v_structName_1397_);
return v___x_1458_;
}
}
else
{
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_a_1408_);
lean_dec_ref(v_e_1399_);
lean_dec(v_idx_1398_);
lean_dec(v_structName_1397_);
return v___x_1456_;
}
}
else
{
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_a_1408_);
lean_dec_ref(v_e_1399_);
lean_dec(v_idx_1398_);
lean_dec(v_structName_1397_);
return v___x_1454_;
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v_a_1430_);
lean_dec(v_numIndices_1427_);
lean_dec(v_numParams_1426_);
lean_dec_ref(v_toConstantVal_1425_);
lean_dec(v_us_1411_);
v___x_1483_ = lean_box(0);
v___x_1484_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1483_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v___x_1484_;
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_numIndices_1427_);
lean_dec(v_numParams_1426_);
lean_dec_ref(v_toConstantVal_1425_);
lean_dec(v_us_1411_);
lean_dec(v_a_1408_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec_ref(v_e_1399_);
lean_dec(v_idx_1398_);
lean_dec(v_structName_1397_);
v_a_1485_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1429_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1429_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_dec_ref(v_ctors_1423_);
lean_dec_ref(v_val_1422_);
lean_dec(v_us_1411_);
goto v___jp_1413_;
}
}
else
{
lean_dec(v_ctors_1423_);
lean_dec_ref(v_val_1422_);
lean_dec(v_us_1411_);
goto v___jp_1413_;
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec(v_val_1421_);
lean_dec(v_us_1411_);
v___x_1493_ = lean_box(0);
v___x_1494_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1493_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v___x_1494_;
}
}
v___jp_1413_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1414_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v___x_1415_;
}
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v___x_1409_);
v___x_1495_ = lean_box(0);
v___x_1496_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(v_structName_1397_, v_idx_1398_, v_e_1399_, v_a_1408_, lean_box(0), v___x_1495_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v___x_1496_;
}
}
else
{
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec_ref(v_e_1399_);
lean_dec(v_idx_1398_);
lean_dec(v_structName_1397_);
return v___x_1407_;
}
}
else
{
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec_ref(v_e_1399_);
lean_dec(v_idx_1398_);
lean_dec(v_structName_1397_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___boxed(lean_object* v_structName_1497_, lean_object* v_idx_1498_, lean_object* v_e_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_structName_1497_, v_idx_1498_, v_e_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* v_upperBound_1506_, lean_object* v_structName_1507_, lean_object* v_e_1508_, lean_object* v_idx_1509_, lean_object* v_a_1510_, lean_object* v_inst_1511_, lean_object* v_R_1512_, lean_object* v_a_1513_, lean_object* v_b_1514_, lean_object* v_c_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(v_upperBound_1506_, v_structName_1507_, v_e_1508_, v_idx_1509_, v_a_1510_, v_a_1513_, v_b_1514_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object* v_upperBound_1522_, lean_object* v_structName_1523_, lean_object* v_e_1524_, lean_object* v_idx_1525_, lean_object* v_a_1526_, lean_object* v_inst_1527_, lean_object* v_R_1528_, lean_object* v_a_1529_, lean_object* v_b_1530_, lean_object* v_c_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(v_upperBound_1522_, v_structName_1523_, v_e_1524_, v_idx_1525_, v_a_1526_, v_inst_1527_, v_R_1528_, v_a_1529_, v_b_1530_, v_c_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v_upperBound_1522_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(lean_object* v_upperBound_1538_, lean_object* v_structName_1539_, lean_object* v_e_1540_, lean_object* v_idx_1541_, lean_object* v_a_1542_, lean_object* v_inst_1543_, lean_object* v_R_1544_, lean_object* v_a_1545_, lean_object* v_b_1546_, lean_object* v_c_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___redArg(v_upperBound_1538_, v_structName_1539_, v_e_1540_, v_idx_1541_, v_a_1542_, v_a_1545_, v_b_1546_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1___boxed(lean_object* v_upperBound_1554_, lean_object* v_structName_1555_, lean_object* v_e_1556_, lean_object* v_idx_1557_, lean_object* v_a_1558_, lean_object* v_inst_1559_, lean_object* v_R_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_, lean_object* v_c_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1_spec__1(v_upperBound_1554_, v_structName_1555_, v_e_1556_, v_idx_1557_, v_a_1558_, v_inst_1559_, v_R_1560_, v_a_1561_, v_b_1562_, v_c_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v_upperBound_1554_);
return v_res_1569_;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_Meta_throwTypeExpected___redArg___closed__0));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* v_type_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1579_ = lean_obj_once(&l_Lean_Meta_throwTypeExpected___redArg___closed__1, &l_Lean_Meta_throwTypeExpected___redArg___closed__1_once, _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1);
v___x_1580_ = l_Lean_indentExpr(v_type_1573_);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_1581_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* v_type_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* v_00_u03b1_1590_, lean_object* v_type_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_type_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Meta_throwTypeExpected(v_00_u03b1_1598_, v_type_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v_ks_1610_; lean_object* v_vs_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1635_; 
v_ks_1610_ = lean_ctor_get(v_x_1606_, 0);
v_vs_1611_ = lean_ctor_get(v_x_1606_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1606_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1613_ = v_x_1606_;
v_isShared_1614_ = v_isSharedCheck_1635_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_vs_1611_);
lean_inc(v_ks_1610_);
lean_dec(v_x_1606_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1635_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = lean_array_get_size(v_ks_1610_);
v___x_1616_ = lean_nat_dec_lt(v_x_1607_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
lean_dec(v_x_1607_);
v___x_1617_ = lean_array_push(v_ks_1610_, v_x_1608_);
v___x_1618_ = lean_array_push(v_vs_1611_, v_x_1609_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 1, v___x_1618_);
lean_ctor_set(v___x_1613_, 0, v___x_1617_);
v___x_1620_ = v___x_1613_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
else
{
lean_object* v_k_x27_1622_; uint8_t v___x_1623_; 
v_k_x27_1622_ = lean_array_fget_borrowed(v_ks_1610_, v_x_1607_);
v___x_1623_ = l_Lean_instBEqMVarId_beq(v_x_1608_, v_k_x27_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1625_; 
if (v_isShared_1614_ == 0)
{
v___x_1625_ = v___x_1613_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_ks_1610_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_vs_1611_);
v___x_1625_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = lean_nat_add(v_x_1607_, v___x_1626_);
lean_dec(v_x_1607_);
v_x_1606_ = v___x_1625_;
v_x_1607_ = v___x_1627_;
goto _start;
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1630_ = lean_array_fset(v_ks_1610_, v_x_1607_, v_x_1608_);
v___x_1631_ = lean_array_fset(v_vs_1611_, v_x_1607_, v_x_1609_);
lean_dec(v_x_1607_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 1, v___x_1631_);
lean_ctor_set(v___x_1613_, 0, v___x_1630_);
v___x_1633_ = v___x_1613_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1636_, lean_object* v_k_1637_, lean_object* v_v_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_1636_, v___x_1639_, v_k_1637_, v_v_1638_);
return v___x_1640_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; 
v___x_1641_ = ((size_t)5ULL);
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_shift_left(v___x_1642_, v___x_1641_);
return v___x_1643_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1644_; size_t v___x_1645_; size_t v___x_1646_; 
v___x_1644_ = ((size_t)1ULL);
v___x_1645_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1646_ = lean_usize_sub(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1648_, size_t v_x_1649_, size_t v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v_es_1653_; size_t v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; size_t v___x_1657_; lean_object* v_j_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_es_1653_ = lean_ctor_get(v_x_1648_, 0);
v___x_1654_ = ((size_t)5ULL);
v___x_1655_ = ((size_t)1ULL);
v___x_1656_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1657_ = lean_usize_land(v_x_1649_, v___x_1656_);
v_j_1658_ = lean_usize_to_nat(v___x_1657_);
v___x_1659_ = lean_array_get_size(v_es_1653_);
v___x_1660_ = lean_nat_dec_lt(v_j_1658_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_dec(v_j_1658_);
lean_dec(v_x_1652_);
lean_dec(v_x_1651_);
return v_x_1648_;
}
else
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1697_; 
lean_inc_ref(v_es_1653_);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_x_1648_, 0);
lean_dec(v_unused_1698_);
v___x_1662_ = v_x_1648_;
v_isShared_1663_ = v_isSharedCheck_1697_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v_x_1648_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1697_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_v_1664_; lean_object* v___x_1665_; lean_object* v_xs_x27_1666_; lean_object* v___y_1668_; 
v_v_1664_ = lean_array_fget(v_es_1653_, v_j_1658_);
v___x_1665_ = lean_box(0);
v_xs_x27_1666_ = lean_array_fset(v_es_1653_, v_j_1658_, v___x_1665_);
switch(lean_obj_tag(v_v_1664_))
{
case 0:
{
lean_object* v_key_1673_; lean_object* v_val_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1684_; 
v_key_1673_ = lean_ctor_get(v_v_1664_, 0);
v_val_1674_ = lean_ctor_get(v_v_1664_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_v_1664_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1676_ = v_v_1664_;
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_val_1674_);
lean_inc(v_key_1673_);
lean_dec(v_v_1664_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
uint8_t v___x_1678_; 
v___x_1678_ = l_Lean_instBEqMVarId_beq(v_x_1651_, v_key_1673_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_del_object(v___x_1676_);
v___x_1679_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1673_, v_val_1674_, v_x_1651_, v_x_1652_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
v___y_1668_ = v___x_1680_;
goto v___jp_1667_;
}
else
{
lean_object* v___x_1682_; 
lean_dec(v_val_1674_);
lean_dec(v_key_1673_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_x_1652_);
lean_ctor_set(v___x_1676_, 0, v_x_1651_);
v___x_1682_ = v___x_1676_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_x_1651_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_x_1652_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v___y_1668_ = v___x_1682_;
goto v___jp_1667_;
}
}
}
}
case 1:
{
lean_object* v_node_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1695_; 
v_node_1685_ = lean_ctor_get(v_v_1664_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_v_1664_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1687_ = v_v_1664_;
v_isShared_1688_ = v_isSharedCheck_1695_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_node_1685_);
lean_dec(v_v_1664_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1695_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1689_ = lean_usize_shift_right(v_x_1649_, v___x_1654_);
v___x_1690_ = lean_usize_add(v_x_1650_, v___x_1655_);
v___x_1691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_node_1685_, v___x_1689_, v___x_1690_, v_x_1651_, v_x_1652_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1691_);
v___x_1693_ = v___x_1687_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v___y_1668_ = v___x_1693_;
goto v___jp_1667_;
}
}
}
default: 
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_x_1651_);
lean_ctor_set(v___x_1696_, 1, v_x_1652_);
v___y_1668_ = v___x_1696_;
goto v___jp_1667_;
}
}
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_array_fset(v_xs_x27_1666_, v_j_1658_, v___y_1668_);
lean_dec(v_j_1658_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1669_);
v___x_1671_ = v___x_1662_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
else
{
lean_object* v_ks_1699_; lean_object* v_vs_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1720_; 
v_ks_1699_ = lean_ctor_get(v_x_1648_, 0);
v_vs_1700_ = lean_ctor_get(v_x_1648_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1702_ = v_x_1648_;
v_isShared_1703_ = v_isSharedCheck_1720_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_vs_1700_);
lean_inc(v_ks_1699_);
lean_dec(v_x_1648_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1720_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_ks_1699_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_vs_1700_);
v___x_1705_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v_newNode_1706_; uint8_t v___y_1708_; size_t v___x_1714_; uint8_t v___x_1715_; 
v_newNode_1706_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1705_, v_x_1651_, v_x_1652_);
v___x_1714_ = ((size_t)7ULL);
v___x_1715_ = lean_usize_dec_le(v___x_1714_, v_x_1650_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1716_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1706_);
v___x_1717_ = lean_unsigned_to_nat(4u);
v___x_1718_ = lean_nat_dec_lt(v___x_1716_, v___x_1717_);
lean_dec(v___x_1716_);
v___y_1708_ = v___x_1718_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___x_1715_;
goto v___jp_1707_;
}
v___jp_1707_:
{
if (v___y_1708_ == 0)
{
lean_object* v_ks_1709_; lean_object* v_vs_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_ks_1709_ = lean_ctor_get(v_newNode_1706_, 0);
lean_inc_ref(v_ks_1709_);
v_vs_1710_ = lean_ctor_get(v_newNode_1706_, 1);
lean_inc_ref(v_vs_1710_);
lean_dec_ref(v_newNode_1706_);
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_1713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1650_, v_ks_1709_, v_vs_1710_, v___x_1711_, v___x_1712_);
lean_dec_ref(v_vs_1710_);
lean_dec_ref(v_ks_1709_);
return v___x_1713_;
}
else
{
return v_newNode_1706_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1721_, lean_object* v_keys_1722_, lean_object* v_vals_1723_, lean_object* v_i_1724_, lean_object* v_entries_1725_){
_start:
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_array_get_size(v_keys_1722_);
v___x_1727_ = lean_nat_dec_lt(v_i_1724_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_dec(v_i_1724_);
return v_entries_1725_;
}
else
{
lean_object* v_k_1728_; lean_object* v_v_1729_; uint64_t v___x_1730_; size_t v_h_1731_; size_t v___x_1732_; lean_object* v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; size_t v_h_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_k_1728_ = lean_array_fget_borrowed(v_keys_1722_, v_i_1724_);
v_v_1729_ = lean_array_fget_borrowed(v_vals_1723_, v_i_1724_);
v___x_1730_ = l_Lean_instHashableMVarId_hash(v_k_1728_);
v_h_1731_ = lean_uint64_to_usize(v___x_1730_);
v___x_1732_ = ((size_t)5ULL);
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_sub(v_depth_1721_, v___x_1734_);
v___x_1736_ = lean_usize_mul(v___x_1732_, v___x_1735_);
v_h_1737_ = lean_usize_shift_right(v_h_1731_, v___x_1736_);
v___x_1738_ = lean_nat_add(v_i_1724_, v___x_1733_);
lean_dec(v_i_1724_);
lean_inc(v_v_1729_);
lean_inc(v_k_1728_);
v___x_1739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_entries_1725_, v_h_1737_, v_depth_1721_, v_k_1728_, v_v_1729_);
v_i_1724_ = v___x_1738_;
v_entries_1725_ = v___x_1739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1741_, lean_object* v_keys_1742_, lean_object* v_vals_1743_, lean_object* v_i_1744_, lean_object* v_entries_1745_){
_start:
{
size_t v_depth_boxed_1746_; lean_object* v_res_1747_; 
v_depth_boxed_1746_ = lean_unbox_usize(v_depth_1741_);
lean_dec(v_depth_1741_);
v_res_1747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1746_, v_keys_1742_, v_vals_1743_, v_i_1744_, v_entries_1745_);
lean_dec_ref(v_vals_1743_);
lean_dec_ref(v_keys_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
size_t v_x_1306__boxed_1753_; size_t v_x_1307__boxed_1754_; lean_object* v_res_1755_; 
v_x_1306__boxed_1753_ = lean_unbox_usize(v_x_1749_);
lean_dec(v_x_1749_);
v_x_1307__boxed_1754_ = lean_unbox_usize(v_x_1750_);
lean_dec(v_x_1750_);
v_res_1755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1748_, v_x_1306__boxed_1753_, v_x_1307__boxed_1754_, v_x_1751_, v_x_1752_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
uint64_t v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1759_ = l_Lean_instHashableMVarId_hash(v_x_1757_);
v___x_1760_ = lean_uint64_to_usize(v___x_1759_);
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1756_, v___x_1760_, v___x_1761_, v_x_1757_, v_x_1758_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(lean_object* v_mvarId_1763_, lean_object* v_val_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v_mctx_1768_; lean_object* v_cache_1769_; lean_object* v_zetaDeltaFVarIds_1770_; lean_object* v_postponed_1771_; lean_object* v_diag_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1799_; 
v___x_1767_ = lean_st_ref_take(v___y_1765_);
v_mctx_1768_ = lean_ctor_get(v___x_1767_, 0);
v_cache_1769_ = lean_ctor_get(v___x_1767_, 1);
v_zetaDeltaFVarIds_1770_ = lean_ctor_get(v___x_1767_, 2);
v_postponed_1771_ = lean_ctor_get(v___x_1767_, 3);
v_diag_1772_ = lean_ctor_get(v___x_1767_, 4);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1774_ = v___x_1767_;
v_isShared_1775_ = v_isSharedCheck_1799_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_diag_1772_);
lean_inc(v_postponed_1771_);
lean_inc(v_zetaDeltaFVarIds_1770_);
lean_inc(v_cache_1769_);
lean_inc(v_mctx_1768_);
lean_dec(v___x_1767_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1799_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_depth_1776_; lean_object* v_levelAssignDepth_1777_; lean_object* v_mvarCounter_1778_; lean_object* v_lDepth_1779_; lean_object* v_decls_1780_; lean_object* v_userNames_1781_; lean_object* v_lAssignment_1782_; lean_object* v_eAssignment_1783_; lean_object* v_dAssignment_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1798_; 
v_depth_1776_ = lean_ctor_get(v_mctx_1768_, 0);
v_levelAssignDepth_1777_ = lean_ctor_get(v_mctx_1768_, 1);
v_mvarCounter_1778_ = lean_ctor_get(v_mctx_1768_, 2);
v_lDepth_1779_ = lean_ctor_get(v_mctx_1768_, 3);
v_decls_1780_ = lean_ctor_get(v_mctx_1768_, 4);
v_userNames_1781_ = lean_ctor_get(v_mctx_1768_, 5);
v_lAssignment_1782_ = lean_ctor_get(v_mctx_1768_, 6);
v_eAssignment_1783_ = lean_ctor_get(v_mctx_1768_, 7);
v_dAssignment_1784_ = lean_ctor_get(v_mctx_1768_, 8);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_mctx_1768_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1786_ = v_mctx_1768_;
v_isShared_1787_ = v_isSharedCheck_1798_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_dAssignment_1784_);
lean_inc(v_eAssignment_1783_);
lean_inc(v_lAssignment_1782_);
lean_inc(v_userNames_1781_);
lean_inc(v_decls_1780_);
lean_inc(v_lDepth_1779_);
lean_inc(v_mvarCounter_1778_);
lean_inc(v_levelAssignDepth_1777_);
lean_inc(v_depth_1776_);
lean_dec(v_mctx_1768_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1798_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_eAssignment_1783_, v_mvarId_1763_, v_val_1764_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 7, v___x_1788_);
v___x_1790_ = v___x_1786_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_depth_1776_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_levelAssignDepth_1777_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_mvarCounter_1778_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_lDepth_1779_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_decls_1780_);
lean_ctor_set(v_reuseFailAlloc_1797_, 5, v_userNames_1781_);
lean_ctor_set(v_reuseFailAlloc_1797_, 6, v_lAssignment_1782_);
lean_ctor_set(v_reuseFailAlloc_1797_, 7, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1797_, 8, v_dAssignment_1784_);
v___x_1790_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1790_);
v___x_1792_ = v___x_1774_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_cache_1769_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_zetaDeltaFVarIds_1770_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_postponed_1771_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_diag_1772_);
v___x_1792_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_st_ref_set(v___y_1765_, v___x_1792_);
v___x_1794_ = lean_box(0);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* v_mvarId_1800_, lean_object* v_val_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1800_, v_val_1801_, v___y_1802_);
lean_dec(v___y_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* v_type_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1811_; 
lean_inc(v_a_1809_);
lean_inc_ref(v_a_1808_);
lean_inc(v_a_1807_);
lean_inc_ref(v_a_1806_);
lean_inc_ref(v_type_1805_);
v___x_1811_ = lean_infer_type(v_type_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
lean_inc(v_a_1809_);
lean_inc_ref(v_a_1808_);
lean_inc(v_a_1807_);
lean_inc_ref(v_a_1806_);
v___x_1813_ = l_Lean_Meta_whnfD(v_a_1812_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1848_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1848_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1848_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
switch(lean_obj_tag(v_a_1814_))
{
case 3:
{
lean_object* v_u_1818_; lean_object* v___x_1820_; 
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec_ref(v_type_1805_);
v_u_1818_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_u_1818_);
lean_dec_ref(v_a_1814_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v_u_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_u_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
case 2:
{
lean_object* v_mvarId_1822_; lean_object* v___x_1823_; 
lean_del_object(v___x_1816_);
v_mvarId_1822_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_mvarId_1822_);
lean_dec_ref(v_a_1814_);
lean_inc(v_mvarId_1822_);
v___x_1823_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1822_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; uint8_t v___x_1825_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = lean_unbox(v_a_1824_);
lean_dec(v_a_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref(v_type_1805_);
v___x_1826_ = l_Lean_Meta_mkFreshLevelMVar(v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec_ref(v_a_1806_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1826_);
lean_inc(v_a_1827_);
v___x_1828_ = l_Lean_mkSort(v_a_1827_);
v___x_1829_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1822_, v___x_1828_, v_a_1807_);
lean_dec(v_a_1807_);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1837_);
v___x_1831_ = v___x_1829_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_a_1827_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1827_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_dec(v_mvarId_1822_);
lean_dec(v_a_1807_);
return v___x_1826_;
}
}
else
{
lean_object* v___x_1838_; 
lean_dec(v_mvarId_1822_);
v___x_1838_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
return v___x_1838_;
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_mvarId_1822_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec_ref(v_type_1805_);
v_a_1839_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1823_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1823_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
default: 
{
lean_object* v___x_1847_; 
lean_del_object(v___x_1816_);
lean_dec(v_a_1814_);
v___x_1847_ = l_Lean_Meta_throwTypeExpected___redArg(v_type_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec_ref(v_type_1805_);
v_a_1849_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1813_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1813_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec_ref(v_type_1805_);
v_a_1857_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1811_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1811_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel___boxed(lean_object* v_type_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Meta_getLevel(v_type_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(lean_object* v_mvarId_1872_, lean_object* v_val_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___redArg(v_mvarId_1872_, v_val_1873_, v___y_1875_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0___boxed(lean_object* v_mvarId_1880_, lean_object* v_val_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0(v_mvarId_1880_, v_val_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0(lean_object* v_00_u03b2_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0___redArg(v_x_1889_, v_x_1890_, v_x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1893_, lean_object* v_x_1894_, size_t v_x_1895_, size_t v_x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg(v_x_1894_, v_x_1895_, v_x_1896_, v_x_1897_, v_x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1900_, lean_object* v_x_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
size_t v_x_1677__boxed_1906_; size_t v_x_1678__boxed_1907_; lean_object* v_res_1908_; 
v_x_1677__boxed_1906_ = lean_unbox_usize(v_x_1902_);
lean_dec(v_x_1902_);
v_x_1678__boxed_1907_ = lean_unbox_usize(v_x_1903_);
lean_dec(v_x_1903_);
v_res_1908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1(v_00_u03b2_1900_, v_x_1901_, v_x_1677__boxed_1906_, v_x_1678__boxed_1907_, v_x_1904_, v_x_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1909_, lean_object* v_n_1910_, lean_object* v_k_1911_, lean_object* v_v_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1910_, v_k_1911_, v_v_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1914_, size_t v_depth_1915_, lean_object* v_keys_1916_, lean_object* v_vals_1917_, lean_object* v_heq_1918_, lean_object* v_i_1919_, lean_object* v_entries_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1915_, v_keys_1916_, v_vals_1917_, v_i_1919_, v_entries_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1922_, lean_object* v_depth_1923_, lean_object* v_keys_1924_, lean_object* v_vals_1925_, lean_object* v_heq_1926_, lean_object* v_i_1927_, lean_object* v_entries_1928_){
_start:
{
size_t v_depth_boxed_1929_; lean_object* v_res_1930_; 
v_depth_boxed_1929_ = lean_unbox_usize(v_depth_1923_);
lean_dec(v_depth_1923_);
v_res_1930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1922_, v_depth_boxed_1929_, v_keys_1924_, v_vals_1925_, v_heq_1926_, v_i_1927_, v_entries_1928_);
lean_dec_ref(v_vals_1925_);
lean_dec_ref(v_keys_1924_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1932_, v_x_1933_, v_x_1934_, v_x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* v_k_1937_, lean_object* v_b_1938_, lean_object* v_c_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_apply_7(v_k_1937_, v_b_1938_, v_c_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, lean_box(0));
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed(lean_object* v_k_1946_, lean_object* v_b_1947_, lean_object* v_c_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(v_k_1946_, v_b_1947_, v_c_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* v_type_1955_, lean_object* v_k_1956_, uint8_t v_cleanupAnnotations_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___f_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1963_, 0, v_k_1956_);
v___x_1964_ = 0;
v___x_1965_ = lean_box(0);
v___x_1966_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1964_, v___x_1965_, v_type_1955_, v___f_1963_, v_cleanupAnnotations_1957_, v___x_1964_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1966_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1966_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* v_type_1983_, lean_object* v_k_1984_, lean_object* v_cleanupAnnotations_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1991_; lean_object* v_res_1992_; 
v_cleanupAnnotations_boxed_1991_ = lean_unbox(v_cleanupAnnotations_1985_);
v_res_1992_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_1983_, v_k_1984_, v_cleanupAnnotations_boxed_1991_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* v_00_u03b1_1993_, lean_object* v_type_1994_, lean_object* v_k_1995_, uint8_t v_cleanupAnnotations_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_type_1994_, v_k_1995_, v_cleanupAnnotations_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_type_2004_, lean_object* v_k_2005_, lean_object* v_cleanupAnnotations_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2012_; lean_object* v_res_2013_; 
v_cleanupAnnotations_boxed_2012_ = lean_unbox(v_cleanupAnnotations_2006_);
v_res_2013_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(v_00_u03b1_2003_, v_type_2004_, v_k_2005_, v_cleanupAnnotations_boxed_2012_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* v_as_2014_, size_t v_i_2015_, size_t v_stop_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_usize_dec_eq(v_i_2015_, v_stop_2016_);
if (v___x_2023_ == 0)
{
size_t v___x_2024_; size_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2024_ = ((size_t)1ULL);
v___x_2025_ = lean_usize_sub(v_i_2015_, v___x_2024_);
v___x_2026_ = lean_array_uget_borrowed(v_as_2014_, v___x_2025_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___x_2026_);
v___x_2027_ = lean_infer_type(v___x_2026_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
v___x_2029_ = l_Lean_Meta_getLevel(v_a_2028_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = l_Lean_mkLevelIMax_x27(v_a_2030_, v_b_2017_);
v_i_2015_ = v___x_2025_;
v_b_2017_ = v___x_2031_;
goto _start;
}
else
{
lean_dec(v_b_2017_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2033_; 
v_a_2033_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2029_);
v_i_2015_ = v___x_2025_;
v_b_2017_ = v_a_2033_;
goto _start;
}
else
{
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v___x_2029_;
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v_b_2017_);
v_a_2035_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2027_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2027_);
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
else
{
lean_object* v___x_2043_; 
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_b_2017_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* v_as_2044_, lean_object* v_i_2045_, lean_object* v_stop_2046_, lean_object* v_b_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
size_t v_i_boxed_2053_; size_t v_stop_boxed_2054_; lean_object* v_res_2055_; 
v_i_boxed_2053_ = lean_unbox_usize(v_i_2045_);
lean_dec(v_i_2045_);
v_stop_boxed_2054_ = lean_unbox_usize(v_stop_2046_);
lean_dec(v_stop_2046_);
v_res_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_as_2044_, v_i_boxed_2053_, v_stop_boxed_2054_, v_b_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec_ref(v_as_2044_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* v_xs_2056_, lean_object* v_e_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___y_2064_; lean_object* v___x_2083_; 
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
v___x_2083_ = l_Lean_Meta_getLevel(v_e_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
v___x_2085_ = lean_array_get_size(v_xs_2056_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_nat_dec_lt(v___x_2086_, v___x_2085_);
if (v___x_2087_ == 0)
{
lean_dec(v_a_2084_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
v___y_2064_ = v___x_2083_;
goto v___jp_2063_;
}
else
{
size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
lean_dec_ref(v___x_2083_);
v___x_2088_ = lean_usize_of_nat(v___x_2085_);
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(v_xs_2056_, v___x_2088_, v___x_2089_, v_a_2084_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
v___y_2064_ = v___x_2090_;
goto v___jp_2063_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
v_a_2091_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2083_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2083_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
v___jp_2063_:
{
if (lean_obj_tag(v___y_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2074_; 
v_a_2065_ = lean_ctor_get(v___y_2064_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___y_2064_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2067_ = v___y_2064_;
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___y_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2069_ = l_Lean_Level_normalize(v_a_2065_);
lean_dec(v_a_2065_);
v___x_2070_ = l_Lean_mkSort(v___x_2069_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2070_);
v___x_2072_ = v___x_2067_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2075_ = lean_ctor_get(v___y_2064_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___y_2064_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___y_2064_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___y_2064_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* v_xs_2099_, lean_object* v_e_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(v_xs_2099_, v_e_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec_ref(v_xs_2099_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* v_e_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___f_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v___f_2114_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__0));
v___x_2115_ = 0;
v___x_2116_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(v_e_2108_, v___f_2114_, v___x_2115_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___boxed(lean_object* v_e_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* v_e_2124_, lean_object* v_k_2125_, uint8_t v_cleanupAnnotations_2126_, uint8_t v_preserveNondepLet_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___f_2133_; uint8_t v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2133_, 0, v_k_2125_);
v___x_2134_ = 1;
v___x_2135_ = 0;
v___x_2136_ = lean_box(0);
v___x_2137_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2124_, v___x_2134_, v___x_2134_, v_preserveNondepLet_2127_, v___x_2135_, v___x_2136_, v___f_2133_, v_cleanupAnnotations_2126_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
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
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
v_a_2146_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2137_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2137_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* v_e_2154_, lean_object* v_k_2155_, lean_object* v_cleanupAnnotations_2156_, lean_object* v_preserveNondepLet_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2163_; uint8_t v_preserveNondepLet_boxed_2164_; lean_object* v_res_2165_; 
v_cleanupAnnotations_boxed_2163_ = lean_unbox(v_cleanupAnnotations_2156_);
v_preserveNondepLet_boxed_2164_ = lean_unbox(v_preserveNondepLet_2157_);
v_res_2165_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2154_, v_k_2155_, v_cleanupAnnotations_boxed_2163_, v_preserveNondepLet_boxed_2164_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* v_00_u03b1_2166_, lean_object* v_e_2167_, lean_object* v_k_2168_, uint8_t v_cleanupAnnotations_2169_, uint8_t v_preserveNondepLet_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2167_, v_k_2168_, v_cleanupAnnotations_2169_, v_preserveNondepLet_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_e_2178_, lean_object* v_k_2179_, lean_object* v_cleanupAnnotations_2180_, lean_object* v_preserveNondepLet_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2187_; uint8_t v_preserveNondepLet_boxed_2188_; lean_object* v_res_2189_; 
v_cleanupAnnotations_boxed_2187_ = lean_unbox(v_cleanupAnnotations_2180_);
v_preserveNondepLet_boxed_2188_ = lean_unbox(v_preserveNondepLet_2181_);
v_res_2189_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(v_00_u03b1_2177_, v_e_2178_, v_k_2179_, v_cleanupAnnotations_boxed_2187_, v_preserveNondepLet_boxed_2188_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* v_xs_2190_, lean_object* v_e_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
v___x_2197_ = lean_infer_type(v_e_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; uint8_t v___x_2199_; uint8_t v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = 0;
v___x_2200_ = 1;
v___x_2201_ = 1;
v___x_2202_ = l_Lean_Meta_mkForallFVars(v_xs_2190_, v_a_2198_, v___x_2199_, v___x_2200_, v___x_2199_, v___x_2201_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v___x_2202_;
}
else
{
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
return v___x_2197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* v_xs_2203_, lean_object* v_e_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(v_xs_2203_, v_e_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec_ref(v_xs_2203_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* v_e_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v___f_2218_; uint8_t v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; 
v___f_2218_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__0));
v___x_2219_ = 0;
v___x_2220_ = 1;
v___x_2221_ = l_Lean_Meta_lambdaLetTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(v_e_2212_, v___f_2218_, v___x_2219_, v___x_2220_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___boxed(lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
return v_res_2228_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__0));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Meta_throwUnknownMVar___redArg___closed__2));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* v_mvarId_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2241_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__1, &l_Lean_Meta_throwUnknownMVar___redArg___closed__1_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
v___x_2242_ = l_Lean_MessageData_ofName(v_mvarId_2235_);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_obj_once(&l_Lean_Meta_throwUnknownMVar___redArg___closed__3, &l_Lean_Meta_throwUnknownMVar___redArg___closed__3_once, _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2245_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* v_mvarId_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* v_00_u03b1_2254_, lean_object* v_mvarId_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* v_00_u03b1_2262_, lean_object* v_mvarId_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Meta_throwUnknownMVar(v_00_u03b1_2262_, v_mvarId_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* v_mvarId_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v_mctx_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_st_ref_get(v_a_2272_);
v_mctx_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc_ref(v_mctx_2277_);
lean_dec(v___x_2276_);
v___x_2278_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2277_, v_mvarId_2270_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Meta_throwUnknownMVar___redArg(v_mvarId_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
return v___x_2279_;
}
else
{
lean_object* v_val_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_mvarId_2270_);
v_val_2280_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2282_ = v___x_2278_;
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_val_2280_);
lean_dec(v___x_2278_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v_type_2284_; lean_object* v___x_2286_; 
v_type_2284_ = lean_ctor_get(v_val_2280_, 2);
lean_inc_ref(v_type_2284_);
lean_dec(v_val_2280_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set_tag(v___x_2282_, 0);
lean_ctor_set(v___x_2282_, 0, v_type_2284_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_type_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* v_mvarId_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* v_fvarId_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_lctx_2301_; lean_object* v___x_2302_; 
v_lctx_2301_ = lean_ctor_get(v_a_2297_, 2);
lean_inc_ref(v_lctx_2301_);
lean_dec_ref(v_a_2297_);
lean_inc(v_fvarId_2296_);
v___x_2302_ = lean_local_ctx_find(v_lctx_2301_, v_fvarId_2296_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2296_, v_a_2298_, v_a_2299_);
return v___x_2303_;
}
else
{
lean_object* v_val_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_fvarId_2296_);
v_val_2304_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2306_ = v___x_2302_;
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_val_2304_);
lean_dec(v___x_2302_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2308_ = l_Lean_LocalDecl_type(v_val_2304_);
lean_dec(v_val_2304_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2308_);
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* v_fvarId_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* v_fvarId_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2319_, v_a_2320_, v_a_2322_, v_a_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* v_fvarId_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(v_fvarId_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* v_e_2335_, lean_object* v_inferType_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
uint8_t v_cacheInferType_2342_; 
v_cacheInferType_2342_ = lean_ctor_get_uint8(v_a_2337_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2342_ == 0)
{
lean_object* v___x_2343_; 
lean_dec_ref(v_e_2335_);
v___x_2343_ = lean_apply_5(v_inferType_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, lean_box(0));
return v___x_2343_;
}
else
{
uint8_t v___x_2344_; 
v___x_2344_ = l_Lean_Expr_hasMVar(v_e_2335_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2335_, v_a_2337_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2399_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2399_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2399_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v_cache_2351_; lean_object* v_inferType_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = lean_st_ref_get(v_a_2338_);
v_cache_2351_ = lean_ctor_get(v___x_2350_, 1);
lean_inc_ref(v_cache_2351_);
lean_dec(v___x_2350_);
v_inferType_2352_ = lean_ctor_get(v_cache_2351_, 0);
lean_inc_ref(v_inferType_2352_);
lean_dec_ref(v_cache_2351_);
v___f_2353_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0));
v___x_2354_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1));
lean_inc(v_a_2346_);
v___x_2355_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2353_, v___x_2354_, v_inferType_2352_, v_a_2346_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2356_; 
lean_del_object(v___x_2348_);
lean_inc(v_a_2338_);
v___x_2356_ = lean_apply_5(v_inferType_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, lean_box(0));
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; uint8_t v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
v___x_2358_ = l_Lean_Expr_hasMVar(v_a_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2393_; 
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2356_, 0);
lean_dec(v_unused_2394_);
v___x_2360_ = v___x_2356_;
v_isShared_2361_ = v_isSharedCheck_2393_;
goto v_resetjp_2359_;
}
else
{
lean_dec(v___x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2393_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v_cache_2363_; lean_object* v_mctx_2364_; lean_object* v_zetaDeltaFVarIds_2365_; lean_object* v_postponed_2366_; lean_object* v_diag_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2392_; 
v___x_2362_ = lean_st_ref_take(v_a_2338_);
v_cache_2363_ = lean_ctor_get(v___x_2362_, 1);
v_mctx_2364_ = lean_ctor_get(v___x_2362_, 0);
v_zetaDeltaFVarIds_2365_ = lean_ctor_get(v___x_2362_, 2);
v_postponed_2366_ = lean_ctor_get(v___x_2362_, 3);
v_diag_2367_ = lean_ctor_get(v___x_2362_, 4);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2369_ = v___x_2362_;
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_diag_2367_);
lean_inc(v_postponed_2366_);
lean_inc(v_zetaDeltaFVarIds_2365_);
lean_inc(v_cache_2363_);
lean_inc(v_mctx_2364_);
lean_dec(v___x_2362_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_inferType_2371_; lean_object* v_funInfo_2372_; lean_object* v_synthInstance_2373_; lean_object* v_whnf_2374_; lean_object* v_defEqTrans_2375_; lean_object* v_defEqPerm_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2391_; 
v_inferType_2371_ = lean_ctor_get(v_cache_2363_, 0);
v_funInfo_2372_ = lean_ctor_get(v_cache_2363_, 1);
v_synthInstance_2373_ = lean_ctor_get(v_cache_2363_, 2);
v_whnf_2374_ = lean_ctor_get(v_cache_2363_, 3);
v_defEqTrans_2375_ = lean_ctor_get(v_cache_2363_, 4);
v_defEqPerm_2376_ = lean_ctor_get(v_cache_2363_, 5);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_cache_2363_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2378_ = v_cache_2363_;
v_isShared_2379_ = v_isSharedCheck_2391_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_defEqPerm_2376_);
lean_inc(v_defEqTrans_2375_);
lean_inc(v_whnf_2374_);
lean_inc(v_synthInstance_2373_);
lean_inc(v_funInfo_2372_);
lean_inc(v_inferType_2371_);
lean_dec(v_cache_2363_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2391_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
lean_inc(v_a_2357_);
v___x_2380_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2353_, v___x_2354_, v_inferType_2371_, v_a_2346_, v_a_2357_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_funInfo_2372_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v_synthInstance_2373_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v_whnf_2374_);
lean_ctor_set(v_reuseFailAlloc_2390_, 4, v_defEqTrans_2375_);
lean_ctor_set(v_reuseFailAlloc_2390_, 5, v_defEqPerm_2376_);
v___x_2382_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2384_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 1, v___x_2382_);
v___x_2384_ = v___x_2369_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_mctx_2364_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_zetaDeltaFVarIds_2365_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v_postponed_2366_);
lean_ctor_set(v_reuseFailAlloc_2389_, 4, v_diag_2367_);
v___x_2384_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2385_ = lean_st_ref_set(v_a_2338_, v___x_2384_);
lean_dec(v_a_2338_);
if (v_isShared_2361_ == 0)
{
v___x_2387_ = v___x_2360_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2357_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2357_);
lean_dec(v_a_2346_);
lean_dec(v_a_2338_);
return v___x_2356_;
}
}
else
{
lean_dec(v_a_2346_);
lean_dec(v_a_2338_);
return v___x_2356_;
}
}
else
{
lean_object* v_val_2395_; lean_object* v___x_2397_; 
lean_dec(v_a_2346_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec_ref(v_inferType_2336_);
v_val_2395_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_val_2395_);
lean_dec_ref(v___x_2355_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v_val_2395_);
v___x_2397_ = v___x_2348_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_val_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec_ref(v_inferType_2336_);
v_a_2400_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2345_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2345_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v___x_2408_; 
lean_dec_ref(v_e_2335_);
v___x_2408_ = lean_apply_5(v_inferType_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, lean_box(0));
return v___x_2408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___boxed(lean_object* v_e_2409_, lean_object* v_inferType_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(v_e_2409_, v_inferType_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* v_x_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___y_2424_; uint8_t v___y_2425_; lean_object* v___y_2426_; uint8_t v___y_2427_; uint8_t v___y_2428_; lean_object* v___y_2429_; uint8_t v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; uint8_t v___y_2463_; lean_object* v___x_2543_; uint8_t v_transparency_2544_; uint8_t v___x_2545_; uint8_t v___x_2546_; 
v___x_2543_ = l_Lean_Meta_Context_config(v_a_2418_);
v_transparency_2544_ = lean_ctor_get_uint8(v___x_2543_, 9);
lean_dec_ref(v___x_2543_);
v___x_2545_ = 1;
v___x_2546_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
v___y_2463_ = v_transparency_2544_;
goto v___jp_2462_;
}
else
{
v___y_2463_ = v___x_2545_;
goto v___jp_2462_;
}
v___jp_2423_:
{
lean_object* v___x_2435_; uint8_t v_foApprox_2436_; uint8_t v_ctxApprox_2437_; uint8_t v_quasiPatternApprox_2438_; uint8_t v_constApprox_2439_; uint8_t v_isDefEqStuckEx_2440_; uint8_t v_unificationHints_2441_; uint8_t v_proofIrrelevance_2442_; uint8_t v_assignSyntheticOpaque_2443_; uint8_t v_offsetCnstrs_2444_; uint8_t v_transparency_2445_; uint8_t v_univApprox_2446_; uint8_t v_zetaUnused_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2461_; 
v___x_2435_ = l_Lean_Meta_Context_config(v___y_2426_);
lean_dec_ref(v___y_2426_);
v_foApprox_2436_ = lean_ctor_get_uint8(v___x_2435_, 0);
v_ctxApprox_2437_ = lean_ctor_get_uint8(v___x_2435_, 1);
v_quasiPatternApprox_2438_ = lean_ctor_get_uint8(v___x_2435_, 2);
v_constApprox_2439_ = lean_ctor_get_uint8(v___x_2435_, 3);
v_isDefEqStuckEx_2440_ = lean_ctor_get_uint8(v___x_2435_, 4);
v_unificationHints_2441_ = lean_ctor_get_uint8(v___x_2435_, 5);
v_proofIrrelevance_2442_ = lean_ctor_get_uint8(v___x_2435_, 6);
v_assignSyntheticOpaque_2443_ = lean_ctor_get_uint8(v___x_2435_, 7);
v_offsetCnstrs_2444_ = lean_ctor_get_uint8(v___x_2435_, 8);
v_transparency_2445_ = lean_ctor_get_uint8(v___x_2435_, 9);
v_univApprox_2446_ = lean_ctor_get_uint8(v___x_2435_, 11);
v_zetaUnused_2447_ = lean_ctor_get_uint8(v___x_2435_, 17);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2449_ = v___x_2435_;
v_isShared_2450_ = v_isSharedCheck_2461_;
goto v_resetjp_2448_;
}
else
{
lean_dec(v___x_2435_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2461_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v___x_2451_; uint8_t v___x_2452_; uint8_t v___x_2453_; lean_object* v___x_2455_; 
v___x_2451_ = 1;
v___x_2452_ = 0;
v___x_2453_ = 2;
if (v_isShared_2450_ == 0)
{
v___x_2455_ = v___x_2449_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 0, v_foApprox_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 1, v_ctxApprox_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 2, v_quasiPatternApprox_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 3, v_constApprox_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 4, v_isDefEqStuckEx_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 5, v_unificationHints_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 6, v_proofIrrelevance_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 7, v_assignSyntheticOpaque_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 8, v_offsetCnstrs_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 9, v_transparency_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 11, v_univApprox_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2460_, 17, v_zetaUnused_2447_);
v___x_2455_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
uint64_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_ctor_set_uint8(v___x_2455_, 10, v___x_2452_);
lean_ctor_set_uint8(v___x_2455_, 12, v___x_2451_);
lean_ctor_set_uint8(v___x_2455_, 13, v___x_2451_);
lean_ctor_set_uint8(v___x_2455_, 14, v___x_2453_);
lean_ctor_set_uint8(v___x_2455_, 15, v___x_2451_);
lean_ctor_set_uint8(v___x_2455_, 16, v___x_2451_);
lean_ctor_set_uint8(v___x_2455_, 18, v___x_2451_);
v___x_2456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2455_);
v___x_2457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set_uint64(v___x_2457_, sizeof(void*)*1, v___x_2456_);
v___x_2458_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v___y_2429_);
lean_ctor_set(v___x_2458_, 2, v___y_2434_);
lean_ctor_set(v___x_2458_, 3, v___y_2431_);
lean_ctor_set(v___x_2458_, 4, v___y_2432_);
lean_ctor_set(v___x_2458_, 5, v___y_2424_);
lean_ctor_set(v___x_2458_, 6, v___y_2433_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7, v___y_2425_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 1, v___y_2427_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 2, v___y_2430_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 3, v___y_2428_);
v___x_2459_ = lean_apply_5(v_x_2417_, v___x_2458_, v_a_2419_, v_a_2420_, v_a_2421_, lean_box(0));
return v___x_2459_;
}
}
}
v___jp_2462_:
{
lean_object* v___x_2464_; uint8_t v_foApprox_2465_; uint8_t v_ctxApprox_2466_; uint8_t v_quasiPatternApprox_2467_; uint8_t v_constApprox_2468_; uint8_t v_isDefEqStuckEx_2469_; uint8_t v_unificationHints_2470_; uint8_t v_proofIrrelevance_2471_; uint8_t v_assignSyntheticOpaque_2472_; uint8_t v_offsetCnstrs_2473_; uint8_t v_etaStruct_2474_; uint8_t v_univApprox_2475_; uint8_t v_iota_2476_; uint8_t v_beta_2477_; uint8_t v_proj_2478_; uint8_t v_zeta_2479_; uint8_t v_zetaDelta_2480_; uint8_t v_zetaUnused_2481_; uint8_t v_zetaHave_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2542_; 
v___x_2464_ = l_Lean_Meta_Context_config(v_a_2418_);
v_foApprox_2465_ = lean_ctor_get_uint8(v___x_2464_, 0);
v_ctxApprox_2466_ = lean_ctor_get_uint8(v___x_2464_, 1);
v_quasiPatternApprox_2467_ = lean_ctor_get_uint8(v___x_2464_, 2);
v_constApprox_2468_ = lean_ctor_get_uint8(v___x_2464_, 3);
v_isDefEqStuckEx_2469_ = lean_ctor_get_uint8(v___x_2464_, 4);
v_unificationHints_2470_ = lean_ctor_get_uint8(v___x_2464_, 5);
v_proofIrrelevance_2471_ = lean_ctor_get_uint8(v___x_2464_, 6);
v_assignSyntheticOpaque_2472_ = lean_ctor_get_uint8(v___x_2464_, 7);
v_offsetCnstrs_2473_ = lean_ctor_get_uint8(v___x_2464_, 8);
v_etaStruct_2474_ = lean_ctor_get_uint8(v___x_2464_, 10);
v_univApprox_2475_ = lean_ctor_get_uint8(v___x_2464_, 11);
v_iota_2476_ = lean_ctor_get_uint8(v___x_2464_, 12);
v_beta_2477_ = lean_ctor_get_uint8(v___x_2464_, 13);
v_proj_2478_ = lean_ctor_get_uint8(v___x_2464_, 14);
v_zeta_2479_ = lean_ctor_get_uint8(v___x_2464_, 15);
v_zetaDelta_2480_ = lean_ctor_get_uint8(v___x_2464_, 16);
v_zetaUnused_2481_ = lean_ctor_get_uint8(v___x_2464_, 17);
v_zetaHave_2482_ = lean_ctor_get_uint8(v___x_2464_, 18);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2484_ = v___x_2464_;
v_isShared_2485_ = v_isSharedCheck_2542_;
goto v_resetjp_2483_;
}
else
{
lean_dec(v___x_2464_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2542_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
uint8_t v_trackZetaDelta_2486_; lean_object* v_zetaDeltaSet_2487_; lean_object* v_lctx_2488_; lean_object* v_localInstances_2489_; lean_object* v_defEqCtx_x3f_2490_; lean_object* v_synthPendingDepth_2491_; lean_object* v_canUnfold_x3f_2492_; uint8_t v_univApprox_2493_; uint8_t v_inTypeClassResolution_2494_; uint8_t v_cacheInferType_2495_; lean_object* v_config_2497_; 
v_trackZetaDelta_2486_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7);
v_zetaDeltaSet_2487_ = lean_ctor_get(v_a_2418_, 1);
lean_inc(v_zetaDeltaSet_2487_);
v_lctx_2488_ = lean_ctor_get(v_a_2418_, 2);
lean_inc_ref(v_lctx_2488_);
v_localInstances_2489_ = lean_ctor_get(v_a_2418_, 3);
lean_inc_ref(v_localInstances_2489_);
v_defEqCtx_x3f_2490_ = lean_ctor_get(v_a_2418_, 4);
lean_inc(v_defEqCtx_x3f_2490_);
v_synthPendingDepth_2491_ = lean_ctor_get(v_a_2418_, 5);
lean_inc(v_synthPendingDepth_2491_);
v_canUnfold_x3f_2492_ = lean_ctor_get(v_a_2418_, 6);
lean_inc(v_canUnfold_x3f_2492_);
v_univApprox_2493_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2494_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7 + 2);
v_cacheInferType_2495_ = lean_ctor_get_uint8(v_a_2418_, sizeof(void*)*7 + 3);
if (v_isShared_2485_ == 0)
{
v_config_2497_ = v___x_2484_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 0, v_foApprox_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 1, v_ctxApprox_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 2, v_quasiPatternApprox_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 3, v_constApprox_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 4, v_isDefEqStuckEx_2469_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 5, v_unificationHints_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 6, v_proofIrrelevance_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 7, v_assignSyntheticOpaque_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 8, v_offsetCnstrs_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 10, v_etaStruct_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 11, v_univApprox_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 12, v_iota_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 13, v_beta_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 14, v_proj_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 15, v_zeta_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 16, v_zetaDelta_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 17, v_zetaUnused_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2541_, 18, v_zetaHave_2482_);
v_config_2497_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
uint64_t v___x_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2533_; 
lean_ctor_set_uint8(v_config_2497_, 9, v___y_2463_);
v___x_2498_ = l_Lean_Meta_Context_configKey(v_a_2418_);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_a_2418_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2534_ = lean_ctor_get(v_a_2418_, 6);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_a_2418_, 5);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_a_2418_, 4);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_a_2418_, 3);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_a_2418_, 2);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_a_2418_, 1);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_a_2418_, 0);
lean_dec(v_unused_2540_);
v___x_2500_ = v_a_2418_;
v_isShared_2501_ = v_isSharedCheck_2533_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v_a_2418_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2533_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
uint64_t v___x_2502_; uint64_t v___x_2503_; uint64_t v___x_2504_; uint64_t v___x_2505_; uint64_t v_key_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2502_ = 2ULL;
v___x_2503_ = lean_uint64_shift_right(v___x_2498_, v___x_2502_);
v___x_2504_ = lean_uint64_shift_left(v___x_2503_, v___x_2502_);
v___x_2505_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2463_);
v_key_2506_ = lean_uint64_lor(v___x_2504_, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2507_, 0, v_config_2497_);
lean_ctor_set_uint64(v___x_2507_, sizeof(void*)*1, v_key_2506_);
lean_inc(v_canUnfold_x3f_2492_);
lean_inc(v_synthPendingDepth_2491_);
lean_inc(v_defEqCtx_x3f_2490_);
lean_inc_ref(v_localInstances_2489_);
lean_inc_ref(v_lctx_2488_);
lean_inc(v_zetaDeltaSet_2487_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2507_);
v___x_2509_ = v___x_2500_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_zetaDeltaSet_2487_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_lctx_2488_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_localInstances_2489_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_defEqCtx_x3f_2490_);
lean_ctor_set(v_reuseFailAlloc_2532_, 5, v_synthPendingDepth_2491_);
lean_ctor_set(v_reuseFailAlloc_2532_, 6, v_canUnfold_x3f_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*7, v_trackZetaDelta_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*7 + 1, v_univApprox_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2494_);
lean_ctor_set_uint8(v_reuseFailAlloc_2532_, sizeof(void*)*7 + 3, v_cacheInferType_2495_);
v___x_2509_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_Meta_getConfig___redArg(v___x_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; uint8_t v_beta_2512_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___x_2510_);
v_beta_2512_ = lean_ctor_get_uint8(v_a_2511_, 13);
if (v_beta_2512_ == 0)
{
lean_dec(v_a_2511_);
v___y_2424_ = v_synthPendingDepth_2491_;
v___y_2425_ = v_trackZetaDelta_2486_;
v___y_2426_ = v___x_2509_;
v___y_2427_ = v_univApprox_2493_;
v___y_2428_ = v_cacheInferType_2495_;
v___y_2429_ = v_zetaDeltaSet_2487_;
v___y_2430_ = v_inTypeClassResolution_2494_;
v___y_2431_ = v_localInstances_2489_;
v___y_2432_ = v_defEqCtx_x3f_2490_;
v___y_2433_ = v_canUnfold_x3f_2492_;
v___y_2434_ = v_lctx_2488_;
goto v___jp_2423_;
}
else
{
uint8_t v_iota_2513_; 
v_iota_2513_ = lean_ctor_get_uint8(v_a_2511_, 12);
if (v_iota_2513_ == 0)
{
lean_dec(v_a_2511_);
v___y_2424_ = v_synthPendingDepth_2491_;
v___y_2425_ = v_trackZetaDelta_2486_;
v___y_2426_ = v___x_2509_;
v___y_2427_ = v_univApprox_2493_;
v___y_2428_ = v_cacheInferType_2495_;
v___y_2429_ = v_zetaDeltaSet_2487_;
v___y_2430_ = v_inTypeClassResolution_2494_;
v___y_2431_ = v_localInstances_2489_;
v___y_2432_ = v_defEqCtx_x3f_2490_;
v___y_2433_ = v_canUnfold_x3f_2492_;
v___y_2434_ = v_lctx_2488_;
goto v___jp_2423_;
}
else
{
uint8_t v_zeta_2514_; 
v_zeta_2514_ = lean_ctor_get_uint8(v_a_2511_, 15);
if (v_zeta_2514_ == 0)
{
lean_dec(v_a_2511_);
v___y_2424_ = v_synthPendingDepth_2491_;
v___y_2425_ = v_trackZetaDelta_2486_;
v___y_2426_ = v___x_2509_;
v___y_2427_ = v_univApprox_2493_;
v___y_2428_ = v_cacheInferType_2495_;
v___y_2429_ = v_zetaDeltaSet_2487_;
v___y_2430_ = v_inTypeClassResolution_2494_;
v___y_2431_ = v_localInstances_2489_;
v___y_2432_ = v_defEqCtx_x3f_2490_;
v___y_2433_ = v_canUnfold_x3f_2492_;
v___y_2434_ = v_lctx_2488_;
goto v___jp_2423_;
}
else
{
uint8_t v_zetaHave_2515_; 
v_zetaHave_2515_ = lean_ctor_get_uint8(v_a_2511_, 18);
if (v_zetaHave_2515_ == 0)
{
lean_dec(v_a_2511_);
v___y_2424_ = v_synthPendingDepth_2491_;
v___y_2425_ = v_trackZetaDelta_2486_;
v___y_2426_ = v___x_2509_;
v___y_2427_ = v_univApprox_2493_;
v___y_2428_ = v_cacheInferType_2495_;
v___y_2429_ = v_zetaDeltaSet_2487_;
v___y_2430_ = v_inTypeClassResolution_2494_;
v___y_2431_ = v_localInstances_2489_;
v___y_2432_ = v_defEqCtx_x3f_2490_;
v___y_2433_ = v_canUnfold_x3f_2492_;
v___y_2434_ = v_lctx_2488_;
goto v___jp_2423_;
}
else
{
uint8_t v_zetaDelta_2516_; 
v_zetaDelta_2516_ = lean_ctor_get_uint8(v_a_2511_, 16);
if (v_zetaDelta_2516_ == 0)
{
lean_dec(v_a_2511_);
v___y_2424_ = v_synthPendingDepth_2491_;
v___y_2425_ = v_trackZetaDelta_2486_;
v___y_2426_ = v___x_2509_;
v___y_2427_ = v_univApprox_2493_;
v___y_2428_ = v_cacheInferType_2495_;
v___y_2429_ = v_zetaDeltaSet_2487_;
v___y_2430_ = v_inTypeClassResolution_2494_;
v___y_2431_ = v_localInstances_2489_;
v___y_2432_ = v_defEqCtx_x3f_2490_;
v___y_2433_ = v_canUnfold_x3f_2492_;
v___y_2434_ = v_lctx_2488_;
goto v___jp_2423_;
}
else
{
uint8_t v_etaStruct_2517_; uint8_t v_proj_2518_; uint8_t v___x_2519_; uint8_t v___x_2520_; 
v_etaStruct_2517_ = lean_ctor_get_uint8(v_a_2511_, 10);
v_proj_2518_ = lean_ctor_get_uint8(v_a_2511_, 14);
lean_dec(v_a_2511_);
v___x_2519_ = 2;
v___x_2520_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
v___y_2424_ = v_synthPendingDepth_2491_;
v___y_2425_ = v_trackZetaDelta_2486_;
v___y_2426_ = v___x_2509_;
v___y_2427_ = v_univApprox_2493_;
v___y_2428_ = v_cacheInferType_2495_;
v___y_2429_ = v_zetaDeltaSet_2487_;
v___y_2430_ = v_inTypeClassResolution_2494_;
v___y_2431_ = v_localInstances_2489_;
v___y_2432_ = v_defEqCtx_x3f_2490_;
v___y_2433_ = v_canUnfold_x3f_2492_;
v___y_2434_ = v_lctx_2488_;
goto v___jp_2423_;
}
else
{
uint8_t v___x_2521_; uint8_t v___x_2522_; 
v___x_2521_ = 0;
v___x_2522_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2517_, v___x_2521_);
if (v___x_2522_ == 0)
{
v___y_2424_ = v_synthPendingDepth_2491_;
v___y_2425_ = v_trackZetaDelta_2486_;
v___y_2426_ = v___x_2509_;
v___y_2427_ = v_univApprox_2493_;
v___y_2428_ = v_cacheInferType_2495_;
v___y_2429_ = v_zetaDeltaSet_2487_;
v___y_2430_ = v_inTypeClassResolution_2494_;
v___y_2431_ = v_localInstances_2489_;
v___y_2432_ = v_defEqCtx_x3f_2490_;
v___y_2433_ = v_canUnfold_x3f_2492_;
v___y_2434_ = v_lctx_2488_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2523_; 
lean_dec(v_canUnfold_x3f_2492_);
lean_dec(v_synthPendingDepth_2491_);
lean_dec(v_defEqCtx_x3f_2490_);
lean_dec_ref(v_localInstances_2489_);
lean_dec_ref(v_lctx_2488_);
lean_dec(v_zetaDeltaSet_2487_);
v___x_2523_ = lean_apply_5(v_x_2417_, v___x_2509_, v_a_2419_, v_a_2420_, v_a_2421_, lean_box(0));
return v___x_2523_;
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
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v___x_2509_);
lean_dec(v_canUnfold_x3f_2492_);
lean_dec(v_synthPendingDepth_2491_);
lean_dec(v_defEqCtx_x3f_2490_);
lean_dec_ref(v_localInstances_2489_);
lean_dec_ref(v_lctx_2488_);
lean_dec(v_zetaDeltaSet_2487_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
lean_dec(v_a_2419_);
lean_dec_ref(v_x_2417_);
v_a_2524_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2510_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2510_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg___boxed(lean_object* v_x_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_withInferTypeConfig___redArg(v_x_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* v_00_u03b1_2554_, lean_object* v_x_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2564_; uint8_t v___y_2565_; uint8_t v___y_2566_; lean_object* v___y_2567_; uint8_t v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; uint8_t v___y_2601_; lean_object* v___x_2681_; uint8_t v_transparency_2682_; uint8_t v___x_2683_; uint8_t v___x_2684_; 
v___x_2681_ = l_Lean_Meta_Context_config(v_a_2556_);
v_transparency_2682_ = lean_ctor_get_uint8(v___x_2681_, 9);
lean_dec_ref(v___x_2681_);
v___x_2683_ = 1;
v___x_2684_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_2682_, v___x_2683_);
if (v___x_2684_ == 0)
{
v___y_2601_ = v_transparency_2682_;
goto v___jp_2600_;
}
else
{
v___y_2601_ = v___x_2683_;
goto v___jp_2600_;
}
v___jp_2561_:
{
lean_object* v___x_2573_; uint8_t v_foApprox_2574_; uint8_t v_ctxApprox_2575_; uint8_t v_quasiPatternApprox_2576_; uint8_t v_constApprox_2577_; uint8_t v_isDefEqStuckEx_2578_; uint8_t v_unificationHints_2579_; uint8_t v_proofIrrelevance_2580_; uint8_t v_assignSyntheticOpaque_2581_; uint8_t v_offsetCnstrs_2582_; uint8_t v_transparency_2583_; uint8_t v_univApprox_2584_; uint8_t v_zetaUnused_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2599_; 
v___x_2573_ = l_Lean_Meta_Context_config(v___y_2564_);
lean_dec_ref(v___y_2564_);
v_foApprox_2574_ = lean_ctor_get_uint8(v___x_2573_, 0);
v_ctxApprox_2575_ = lean_ctor_get_uint8(v___x_2573_, 1);
v_quasiPatternApprox_2576_ = lean_ctor_get_uint8(v___x_2573_, 2);
v_constApprox_2577_ = lean_ctor_get_uint8(v___x_2573_, 3);
v_isDefEqStuckEx_2578_ = lean_ctor_get_uint8(v___x_2573_, 4);
v_unificationHints_2579_ = lean_ctor_get_uint8(v___x_2573_, 5);
v_proofIrrelevance_2580_ = lean_ctor_get_uint8(v___x_2573_, 6);
v_assignSyntheticOpaque_2581_ = lean_ctor_get_uint8(v___x_2573_, 7);
v_offsetCnstrs_2582_ = lean_ctor_get_uint8(v___x_2573_, 8);
v_transparency_2583_ = lean_ctor_get_uint8(v___x_2573_, 9);
v_univApprox_2584_ = lean_ctor_get_uint8(v___x_2573_, 11);
v_zetaUnused_2585_ = lean_ctor_get_uint8(v___x_2573_, 17);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2587_ = v___x_2573_;
v_isShared_2588_ = v_isSharedCheck_2599_;
goto v_resetjp_2586_;
}
else
{
lean_dec(v___x_2573_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2599_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
uint8_t v___x_2589_; uint8_t v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2593_; 
v___x_2589_ = 1;
v___x_2590_ = 0;
v___x_2591_ = 2;
if (v_isShared_2588_ == 0)
{
v___x_2593_ = v___x_2587_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 0, v_foApprox_2574_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 1, v_ctxApprox_2575_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 2, v_quasiPatternApprox_2576_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 3, v_constApprox_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 4, v_isDefEqStuckEx_2578_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 5, v_unificationHints_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 6, v_proofIrrelevance_2580_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 7, v_assignSyntheticOpaque_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 8, v_offsetCnstrs_2582_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 9, v_transparency_2583_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 11, v_univApprox_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2598_, 17, v_zetaUnused_2585_);
v___x_2593_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
uint64_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_ctor_set_uint8(v___x_2593_, 10, v___x_2590_);
lean_ctor_set_uint8(v___x_2593_, 12, v___x_2589_);
lean_ctor_set_uint8(v___x_2593_, 13, v___x_2589_);
lean_ctor_set_uint8(v___x_2593_, 14, v___x_2591_);
lean_ctor_set_uint8(v___x_2593_, 15, v___x_2589_);
lean_ctor_set_uint8(v___x_2593_, 16, v___x_2589_);
lean_ctor_set_uint8(v___x_2593_, 18, v___x_2589_);
v___x_2594_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set_uint64(v___x_2595_, sizeof(void*)*1, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___y_2567_);
lean_ctor_set(v___x_2596_, 2, v___y_2572_);
lean_ctor_set(v___x_2596_, 3, v___y_2569_);
lean_ctor_set(v___x_2596_, 4, v___y_2570_);
lean_ctor_set(v___x_2596_, 5, v___y_2562_);
lean_ctor_set(v___x_2596_, 6, v___y_2571_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*7, v___y_2563_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*7 + 1, v___y_2565_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*7 + 2, v___y_2568_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*7 + 3, v___y_2566_);
v___x_2597_ = lean_apply_5(v_x_2555_, v___x_2596_, v_a_2557_, v_a_2558_, v_a_2559_, lean_box(0));
return v___x_2597_;
}
}
}
v___jp_2600_:
{
lean_object* v___x_2602_; uint8_t v_foApprox_2603_; uint8_t v_ctxApprox_2604_; uint8_t v_quasiPatternApprox_2605_; uint8_t v_constApprox_2606_; uint8_t v_isDefEqStuckEx_2607_; uint8_t v_unificationHints_2608_; uint8_t v_proofIrrelevance_2609_; uint8_t v_assignSyntheticOpaque_2610_; uint8_t v_offsetCnstrs_2611_; uint8_t v_etaStruct_2612_; uint8_t v_univApprox_2613_; uint8_t v_iota_2614_; uint8_t v_beta_2615_; uint8_t v_proj_2616_; uint8_t v_zeta_2617_; uint8_t v_zetaDelta_2618_; uint8_t v_zetaUnused_2619_; uint8_t v_zetaHave_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2680_; 
v___x_2602_ = l_Lean_Meta_Context_config(v_a_2556_);
v_foApprox_2603_ = lean_ctor_get_uint8(v___x_2602_, 0);
v_ctxApprox_2604_ = lean_ctor_get_uint8(v___x_2602_, 1);
v_quasiPatternApprox_2605_ = lean_ctor_get_uint8(v___x_2602_, 2);
v_constApprox_2606_ = lean_ctor_get_uint8(v___x_2602_, 3);
v_isDefEqStuckEx_2607_ = lean_ctor_get_uint8(v___x_2602_, 4);
v_unificationHints_2608_ = lean_ctor_get_uint8(v___x_2602_, 5);
v_proofIrrelevance_2609_ = lean_ctor_get_uint8(v___x_2602_, 6);
v_assignSyntheticOpaque_2610_ = lean_ctor_get_uint8(v___x_2602_, 7);
v_offsetCnstrs_2611_ = lean_ctor_get_uint8(v___x_2602_, 8);
v_etaStruct_2612_ = lean_ctor_get_uint8(v___x_2602_, 10);
v_univApprox_2613_ = lean_ctor_get_uint8(v___x_2602_, 11);
v_iota_2614_ = lean_ctor_get_uint8(v___x_2602_, 12);
v_beta_2615_ = lean_ctor_get_uint8(v___x_2602_, 13);
v_proj_2616_ = lean_ctor_get_uint8(v___x_2602_, 14);
v_zeta_2617_ = lean_ctor_get_uint8(v___x_2602_, 15);
v_zetaDelta_2618_ = lean_ctor_get_uint8(v___x_2602_, 16);
v_zetaUnused_2619_ = lean_ctor_get_uint8(v___x_2602_, 17);
v_zetaHave_2620_ = lean_ctor_get_uint8(v___x_2602_, 18);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2622_ = v___x_2602_;
v_isShared_2623_ = v_isSharedCheck_2680_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v___x_2602_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2680_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
uint8_t v_trackZetaDelta_2624_; lean_object* v_zetaDeltaSet_2625_; lean_object* v_lctx_2626_; lean_object* v_localInstances_2627_; lean_object* v_defEqCtx_x3f_2628_; lean_object* v_synthPendingDepth_2629_; lean_object* v_canUnfold_x3f_2630_; uint8_t v_univApprox_2631_; uint8_t v_inTypeClassResolution_2632_; uint8_t v_cacheInferType_2633_; lean_object* v_config_2635_; 
v_trackZetaDelta_2624_ = lean_ctor_get_uint8(v_a_2556_, sizeof(void*)*7);
v_zetaDeltaSet_2625_ = lean_ctor_get(v_a_2556_, 1);
lean_inc(v_zetaDeltaSet_2625_);
v_lctx_2626_ = lean_ctor_get(v_a_2556_, 2);
lean_inc_ref(v_lctx_2626_);
v_localInstances_2627_ = lean_ctor_get(v_a_2556_, 3);
lean_inc_ref(v_localInstances_2627_);
v_defEqCtx_x3f_2628_ = lean_ctor_get(v_a_2556_, 4);
lean_inc(v_defEqCtx_x3f_2628_);
v_synthPendingDepth_2629_ = lean_ctor_get(v_a_2556_, 5);
lean_inc(v_synthPendingDepth_2629_);
v_canUnfold_x3f_2630_ = lean_ctor_get(v_a_2556_, 6);
lean_inc(v_canUnfold_x3f_2630_);
v_univApprox_2631_ = lean_ctor_get_uint8(v_a_2556_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2632_ = lean_ctor_get_uint8(v_a_2556_, sizeof(void*)*7 + 2);
v_cacheInferType_2633_ = lean_ctor_get_uint8(v_a_2556_, sizeof(void*)*7 + 3);
if (v_isShared_2623_ == 0)
{
v_config_2635_ = v___x_2622_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 0, v_foApprox_2603_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 1, v_ctxApprox_2604_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 2, v_quasiPatternApprox_2605_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 3, v_constApprox_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 4, v_isDefEqStuckEx_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 5, v_unificationHints_2608_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 6, v_proofIrrelevance_2609_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 7, v_assignSyntheticOpaque_2610_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 8, v_offsetCnstrs_2611_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 10, v_etaStruct_2612_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 11, v_univApprox_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 12, v_iota_2614_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 13, v_beta_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 14, v_proj_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 15, v_zeta_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 16, v_zetaDelta_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 17, v_zetaUnused_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 18, v_zetaHave_2620_);
v_config_2635_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
uint64_t v___x_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2671_; 
lean_ctor_set_uint8(v_config_2635_, 9, v___y_2601_);
v___x_2636_ = l_Lean_Meta_Context_configKey(v_a_2556_);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_a_2556_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; lean_object* v_unused_2673_; lean_object* v_unused_2674_; lean_object* v_unused_2675_; lean_object* v_unused_2676_; lean_object* v_unused_2677_; lean_object* v_unused_2678_; 
v_unused_2672_ = lean_ctor_get(v_a_2556_, 6);
lean_dec(v_unused_2672_);
v_unused_2673_ = lean_ctor_get(v_a_2556_, 5);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_a_2556_, 4);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_a_2556_, 3);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_a_2556_, 2);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_a_2556_, 1);
lean_dec(v_unused_2677_);
v_unused_2678_ = lean_ctor_get(v_a_2556_, 0);
lean_dec(v_unused_2678_);
v___x_2638_ = v_a_2556_;
v_isShared_2639_ = v_isSharedCheck_2671_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v_a_2556_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2671_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
uint64_t v___x_2640_; uint64_t v___x_2641_; uint64_t v___x_2642_; uint64_t v___x_2643_; uint64_t v_key_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2640_ = 2ULL;
v___x_2641_ = lean_uint64_shift_right(v___x_2636_, v___x_2640_);
v___x_2642_ = lean_uint64_shift_left(v___x_2641_, v___x_2640_);
v___x_2643_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_2601_);
v_key_2644_ = lean_uint64_lor(v___x_2642_, v___x_2643_);
v___x_2645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2645_, 0, v_config_2635_);
lean_ctor_set_uint64(v___x_2645_, sizeof(void*)*1, v_key_2644_);
lean_inc(v_canUnfold_x3f_2630_);
lean_inc(v_synthPendingDepth_2629_);
lean_inc(v_defEqCtx_x3f_2628_);
lean_inc_ref(v_localInstances_2627_);
lean_inc_ref(v_lctx_2626_);
lean_inc(v_zetaDeltaSet_2625_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2645_);
v___x_2647_ = v___x_2638_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_zetaDeltaSet_2625_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_lctx_2626_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_localInstances_2627_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_defEqCtx_x3f_2628_);
lean_ctor_set(v_reuseFailAlloc_2670_, 5, v_synthPendingDepth_2629_);
lean_ctor_set(v_reuseFailAlloc_2670_, 6, v_canUnfold_x3f_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7, v_trackZetaDelta_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 1, v_univApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2670_, sizeof(void*)*7 + 3, v_cacheInferType_2633_);
v___x_2647_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_Meta_getConfig___redArg(v___x_2647_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; uint8_t v_beta_2650_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v_beta_2650_ = lean_ctor_get_uint8(v_a_2649_, 13);
if (v_beta_2650_ == 0)
{
lean_dec(v_a_2649_);
v___y_2562_ = v_synthPendingDepth_2629_;
v___y_2563_ = v_trackZetaDelta_2624_;
v___y_2564_ = v___x_2647_;
v___y_2565_ = v_univApprox_2631_;
v___y_2566_ = v_cacheInferType_2633_;
v___y_2567_ = v_zetaDeltaSet_2625_;
v___y_2568_ = v_inTypeClassResolution_2632_;
v___y_2569_ = v_localInstances_2627_;
v___y_2570_ = v_defEqCtx_x3f_2628_;
v___y_2571_ = v_canUnfold_x3f_2630_;
v___y_2572_ = v_lctx_2626_;
goto v___jp_2561_;
}
else
{
uint8_t v_iota_2651_; 
v_iota_2651_ = lean_ctor_get_uint8(v_a_2649_, 12);
if (v_iota_2651_ == 0)
{
lean_dec(v_a_2649_);
v___y_2562_ = v_synthPendingDepth_2629_;
v___y_2563_ = v_trackZetaDelta_2624_;
v___y_2564_ = v___x_2647_;
v___y_2565_ = v_univApprox_2631_;
v___y_2566_ = v_cacheInferType_2633_;
v___y_2567_ = v_zetaDeltaSet_2625_;
v___y_2568_ = v_inTypeClassResolution_2632_;
v___y_2569_ = v_localInstances_2627_;
v___y_2570_ = v_defEqCtx_x3f_2628_;
v___y_2571_ = v_canUnfold_x3f_2630_;
v___y_2572_ = v_lctx_2626_;
goto v___jp_2561_;
}
else
{
uint8_t v_zeta_2652_; 
v_zeta_2652_ = lean_ctor_get_uint8(v_a_2649_, 15);
if (v_zeta_2652_ == 0)
{
lean_dec(v_a_2649_);
v___y_2562_ = v_synthPendingDepth_2629_;
v___y_2563_ = v_trackZetaDelta_2624_;
v___y_2564_ = v___x_2647_;
v___y_2565_ = v_univApprox_2631_;
v___y_2566_ = v_cacheInferType_2633_;
v___y_2567_ = v_zetaDeltaSet_2625_;
v___y_2568_ = v_inTypeClassResolution_2632_;
v___y_2569_ = v_localInstances_2627_;
v___y_2570_ = v_defEqCtx_x3f_2628_;
v___y_2571_ = v_canUnfold_x3f_2630_;
v___y_2572_ = v_lctx_2626_;
goto v___jp_2561_;
}
else
{
uint8_t v_zetaHave_2653_; 
v_zetaHave_2653_ = lean_ctor_get_uint8(v_a_2649_, 18);
if (v_zetaHave_2653_ == 0)
{
lean_dec(v_a_2649_);
v___y_2562_ = v_synthPendingDepth_2629_;
v___y_2563_ = v_trackZetaDelta_2624_;
v___y_2564_ = v___x_2647_;
v___y_2565_ = v_univApprox_2631_;
v___y_2566_ = v_cacheInferType_2633_;
v___y_2567_ = v_zetaDeltaSet_2625_;
v___y_2568_ = v_inTypeClassResolution_2632_;
v___y_2569_ = v_localInstances_2627_;
v___y_2570_ = v_defEqCtx_x3f_2628_;
v___y_2571_ = v_canUnfold_x3f_2630_;
v___y_2572_ = v_lctx_2626_;
goto v___jp_2561_;
}
else
{
uint8_t v_zetaDelta_2654_; 
v_zetaDelta_2654_ = lean_ctor_get_uint8(v_a_2649_, 16);
if (v_zetaDelta_2654_ == 0)
{
lean_dec(v_a_2649_);
v___y_2562_ = v_synthPendingDepth_2629_;
v___y_2563_ = v_trackZetaDelta_2624_;
v___y_2564_ = v___x_2647_;
v___y_2565_ = v_univApprox_2631_;
v___y_2566_ = v_cacheInferType_2633_;
v___y_2567_ = v_zetaDeltaSet_2625_;
v___y_2568_ = v_inTypeClassResolution_2632_;
v___y_2569_ = v_localInstances_2627_;
v___y_2570_ = v_defEqCtx_x3f_2628_;
v___y_2571_ = v_canUnfold_x3f_2630_;
v___y_2572_ = v_lctx_2626_;
goto v___jp_2561_;
}
else
{
uint8_t v_etaStruct_2655_; uint8_t v_proj_2656_; uint8_t v___x_2657_; uint8_t v___x_2658_; 
v_etaStruct_2655_ = lean_ctor_get_uint8(v_a_2649_, 10);
v_proj_2656_ = lean_ctor_get_uint8(v_a_2649_, 14);
lean_dec(v_a_2649_);
v___x_2657_ = 2;
v___x_2658_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_2656_, v___x_2657_);
if (v___x_2658_ == 0)
{
v___y_2562_ = v_synthPendingDepth_2629_;
v___y_2563_ = v_trackZetaDelta_2624_;
v___y_2564_ = v___x_2647_;
v___y_2565_ = v_univApprox_2631_;
v___y_2566_ = v_cacheInferType_2633_;
v___y_2567_ = v_zetaDeltaSet_2625_;
v___y_2568_ = v_inTypeClassResolution_2632_;
v___y_2569_ = v_localInstances_2627_;
v___y_2570_ = v_defEqCtx_x3f_2628_;
v___y_2571_ = v_canUnfold_x3f_2630_;
v___y_2572_ = v_lctx_2626_;
goto v___jp_2561_;
}
else
{
uint8_t v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = 0;
v___x_2660_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_2655_, v___x_2659_);
if (v___x_2660_ == 0)
{
v___y_2562_ = v_synthPendingDepth_2629_;
v___y_2563_ = v_trackZetaDelta_2624_;
v___y_2564_ = v___x_2647_;
v___y_2565_ = v_univApprox_2631_;
v___y_2566_ = v_cacheInferType_2633_;
v___y_2567_ = v_zetaDeltaSet_2625_;
v___y_2568_ = v_inTypeClassResolution_2632_;
v___y_2569_ = v_localInstances_2627_;
v___y_2570_ = v_defEqCtx_x3f_2628_;
v___y_2571_ = v_canUnfold_x3f_2630_;
v___y_2572_ = v_lctx_2626_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2661_; 
lean_dec(v_canUnfold_x3f_2630_);
lean_dec(v_synthPendingDepth_2629_);
lean_dec(v_defEqCtx_x3f_2628_);
lean_dec_ref(v_localInstances_2627_);
lean_dec_ref(v_lctx_2626_);
lean_dec(v_zetaDeltaSet_2625_);
v___x_2661_ = lean_apply_5(v_x_2555_, v___x_2647_, v_a_2557_, v_a_2558_, v_a_2559_, lean_box(0));
return v___x_2661_;
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
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v___x_2647_);
lean_dec(v_canUnfold_x3f_2630_);
lean_dec(v_synthPendingDepth_2629_);
lean_dec(v_defEqCtx_x3f_2628_);
lean_dec_ref(v_localInstances_2627_);
lean_dec_ref(v_lctx_2626_);
lean_dec(v_zetaDeltaSet_2625_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_x_2555_);
v_a_2662_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2648_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2648_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___boxed(lean_object* v_00_u03b1_2685_, lean_object* v_x_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_Meta_withInferTypeConfig(v_00_u03b1_2685_, v_x_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_2693_, lean_object* v_x_2694_, lean_object* v_x_2695_, lean_object* v_x_2696_){
_start:
{
lean_object* v_ks_2697_; lean_object* v_vs_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2727_; 
v_ks_2697_ = lean_ctor_get(v_x_2693_, 0);
v_vs_2698_ = lean_ctor_get(v_x_2693_, 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_x_2693_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2700_ = v_x_2693_;
v_isShared_2701_ = v_isSharedCheck_2727_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_vs_2698_);
lean_inc(v_ks_2697_);
lean_dec(v_x_2693_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2727_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
uint8_t v___y_2703_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = lean_array_get_size(v_ks_2697_);
v___x_2716_ = lean_nat_dec_lt(v_x_2694_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_del_object(v___x_2700_);
lean_dec(v_x_2694_);
v___x_2717_ = lean_array_push(v_ks_2697_, v_x_2695_);
v___x_2718_ = lean_array_push(v_vs_2698_, v_x_2696_);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
return v___x_2719_;
}
else
{
lean_object* v_expr_2720_; uint64_t v_configKey_2721_; lean_object* v_k_x27_2722_; lean_object* v_expr_2723_; uint64_t v_configKey_2724_; uint8_t v___x_2725_; 
v_expr_2720_ = lean_ctor_get(v_x_2695_, 0);
v_configKey_2721_ = lean_ctor_get_uint64(v_x_2695_, sizeof(void*)*1);
v_k_x27_2722_ = lean_array_fget_borrowed(v_ks_2697_, v_x_2694_);
v_expr_2723_ = lean_ctor_get(v_k_x27_2722_, 0);
v_configKey_2724_ = lean_ctor_get_uint64(v_k_x27_2722_, sizeof(void*)*1);
v___x_2725_ = lean_expr_equal(v_expr_2720_, v_expr_2723_);
if (v___x_2725_ == 0)
{
v___y_2703_ = v___x_2725_;
goto v___jp_2702_;
}
else
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_uint64_dec_eq(v_configKey_2721_, v_configKey_2724_);
v___y_2703_ = v___x_2726_;
goto v___jp_2702_;
}
}
v___jp_2702_:
{
if (v___y_2703_ == 0)
{
lean_object* v___x_2705_; 
if (v_isShared_2701_ == 0)
{
v___x_2705_ = v___x_2700_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_ks_2697_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_vs_2698_);
v___x_2705_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_nat_add(v_x_2694_, v___x_2706_);
lean_dec(v_x_2694_);
v_x_2693_ = v___x_2705_;
v_x_2694_ = v___x_2707_;
goto _start;
}
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2710_ = lean_array_fset(v_ks_2697_, v_x_2694_, v_x_2695_);
v___x_2711_ = lean_array_fset(v_vs_2698_, v_x_2694_, v_x_2696_);
lean_dec(v_x_2694_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2711_);
lean_ctor_set(v___x_2700_, 0, v___x_2710_);
v___x_2713_ = v___x_2700_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(lean_object* v_n_2728_, lean_object* v_k_2729_, lean_object* v_v_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2728_, v___x_2731_, v_k_2729_, v_v_2730_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(lean_object* v_x_2734_, size_t v_x_2735_, size_t v_x_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_){
_start:
{
if (lean_obj_tag(v_x_2734_) == 0)
{
lean_object* v_es_2739_; size_t v___x_2740_; size_t v___x_2741_; size_t v___x_2742_; size_t v___x_2743_; lean_object* v_j_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v_es_2739_ = lean_ctor_get(v_x_2734_, 0);
v___x_2740_ = ((size_t)5ULL);
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2743_ = lean_usize_land(v_x_2735_, v___x_2742_);
v_j_2744_ = lean_usize_to_nat(v___x_2743_);
v___x_2745_ = lean_array_get_size(v_es_2739_);
v___x_2746_ = lean_nat_dec_lt(v_j_2744_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_dec(v_j_2744_);
lean_dec(v_x_2738_);
lean_dec_ref(v_x_2737_);
return v_x_2734_;
}
else
{
lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2790_; 
lean_inc_ref(v_es_2739_);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_x_2734_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v_x_2734_, 0);
lean_dec(v_unused_2791_);
v___x_2748_ = v_x_2734_;
v_isShared_2749_ = v_isSharedCheck_2790_;
goto v_resetjp_2747_;
}
else
{
lean_dec(v_x_2734_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2790_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_v_2750_; lean_object* v___x_2751_; lean_object* v_xs_x27_2752_; lean_object* v___y_2754_; 
v_v_2750_ = lean_array_fget(v_es_2739_, v_j_2744_);
v___x_2751_ = lean_box(0);
v_xs_x27_2752_ = lean_array_fset(v_es_2739_, v_j_2744_, v___x_2751_);
switch(lean_obj_tag(v_v_2750_))
{
case 0:
{
lean_object* v_key_2759_; lean_object* v_val_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2777_; 
v_key_2759_ = lean_ctor_get(v_v_2750_, 0);
v_val_2760_ = lean_ctor_get(v_v_2750_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_v_2750_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2762_ = v_v_2750_;
v_isShared_2763_ = v_isSharedCheck_2777_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_val_2760_);
lean_inc(v_key_2759_);
lean_dec(v_v_2750_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2777_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
uint8_t v___y_2765_; lean_object* v_expr_2771_; uint64_t v_configKey_2772_; lean_object* v_expr_2773_; uint64_t v_configKey_2774_; uint8_t v___x_2775_; 
v_expr_2771_ = lean_ctor_get(v_x_2737_, 0);
v_configKey_2772_ = lean_ctor_get_uint64(v_x_2737_, sizeof(void*)*1);
v_expr_2773_ = lean_ctor_get(v_key_2759_, 0);
v_configKey_2774_ = lean_ctor_get_uint64(v_key_2759_, sizeof(void*)*1);
v___x_2775_ = lean_expr_equal(v_expr_2771_, v_expr_2773_);
if (v___x_2775_ == 0)
{
v___y_2765_ = v___x_2775_;
goto v___jp_2764_;
}
else
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_uint64_dec_eq(v_configKey_2772_, v_configKey_2774_);
v___y_2765_ = v___x_2776_;
goto v___jp_2764_;
}
v___jp_2764_:
{
if (v___y_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_del_object(v___x_2762_);
v___x_2766_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2759_, v_val_2760_, v_x_2737_, v_x_2738_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v___y_2754_ = v___x_2767_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2769_; 
lean_dec(v_val_2760_);
lean_dec(v_key_2759_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 1, v_x_2738_);
lean_ctor_set(v___x_2762_, 0, v_x_2737_);
v___x_2769_ = v___x_2762_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_x_2737_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_x_2738_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
v___y_2754_ = v___x_2769_;
goto v___jp_2753_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2788_; 
v_node_2778_ = lean_ctor_get(v_v_2750_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_v_2750_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2780_ = v_v_2750_;
v_isShared_2781_ = v_isSharedCheck_2788_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_node_2778_);
lean_dec(v_v_2750_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2788_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
size_t v___x_2782_; size_t v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2782_ = lean_usize_shift_right(v_x_2735_, v___x_2740_);
v___x_2783_ = lean_usize_add(v_x_2736_, v___x_2741_);
v___x_2784_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_node_2778_, v___x_2782_, v___x_2783_, v_x_2737_, v_x_2738_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2784_);
v___x_2786_ = v___x_2780_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
v___y_2754_ = v___x_2786_;
goto v___jp_2753_;
}
}
}
default: 
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v_x_2737_);
lean_ctor_set(v___x_2789_, 1, v_x_2738_);
v___y_2754_ = v___x_2789_;
goto v___jp_2753_;
}
}
v___jp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = lean_array_fset(v_xs_x27_2752_, v_j_2744_, v___y_2754_);
lean_dec(v_j_2744_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2755_);
v___x_2757_ = v___x_2748_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
else
{
lean_object* v_ks_2792_; lean_object* v_vs_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2813_; 
v_ks_2792_ = lean_ctor_get(v_x_2734_, 0);
v_vs_2793_ = lean_ctor_get(v_x_2734_, 1);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_x_2734_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2795_ = v_x_2734_;
v_isShared_2796_ = v_isSharedCheck_2813_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_vs_2793_);
lean_inc(v_ks_2792_);
lean_dec(v_x_2734_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2813_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_ks_2792_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_vs_2793_);
v___x_2798_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v_newNode_2799_; uint8_t v___y_2801_; size_t v___x_2807_; uint8_t v___x_2808_; 
v_newNode_2799_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v___x_2798_, v_x_2737_, v_x_2738_);
v___x_2807_ = ((size_t)7ULL);
v___x_2808_ = lean_usize_dec_le(v___x_2807_, v_x_2736_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2809_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2799_);
v___x_2810_ = lean_unsigned_to_nat(4u);
v___x_2811_ = lean_nat_dec_lt(v___x_2809_, v___x_2810_);
lean_dec(v___x_2809_);
v___y_2801_ = v___x_2811_;
goto v___jp_2800_;
}
else
{
v___y_2801_ = v___x_2808_;
goto v___jp_2800_;
}
v___jp_2800_:
{
if (v___y_2801_ == 0)
{
lean_object* v_ks_2802_; lean_object* v_vs_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_ks_2802_ = lean_ctor_get(v_newNode_2799_, 0);
lean_inc_ref(v_ks_2802_);
v_vs_2803_ = lean_ctor_get(v_newNode_2799_, 1);
lean_inc_ref(v_vs_2803_);
lean_dec_ref(v_newNode_2799_);
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___closed__0);
v___x_2806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_x_2736_, v_ks_2802_, v_vs_2803_, v___x_2804_, v___x_2805_);
lean_dec_ref(v_vs_2803_);
lean_dec_ref(v_ks_2802_);
return v___x_2806_;
}
else
{
return v_newNode_2799_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(size_t v_depth_2814_, lean_object* v_keys_2815_, lean_object* v_vals_2816_, lean_object* v_i_2817_, lean_object* v_entries_2818_){
_start:
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = lean_array_get_size(v_keys_2815_);
v___x_2820_ = lean_nat_dec_lt(v_i_2817_, v___x_2819_);
if (v___x_2820_ == 0)
{
lean_dec(v_i_2817_);
return v_entries_2818_;
}
else
{
lean_object* v_k_2821_; lean_object* v_expr_2822_; uint64_t v_configKey_2823_; lean_object* v_v_2824_; uint64_t v___x_2825_; uint64_t v___x_2826_; size_t v_h_2827_; size_t v___x_2828_; lean_object* v___x_2829_; size_t v___x_2830_; size_t v___x_2831_; size_t v___x_2832_; size_t v_h_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_k_2821_ = lean_array_fget_borrowed(v_keys_2815_, v_i_2817_);
v_expr_2822_ = lean_ctor_get(v_k_2821_, 0);
v_configKey_2823_ = lean_ctor_get_uint64(v_k_2821_, sizeof(void*)*1);
v_v_2824_ = lean_array_fget_borrowed(v_vals_2816_, v_i_2817_);
v___x_2825_ = l_Lean_Expr_hash(v_expr_2822_);
v___x_2826_ = lean_uint64_mix_hash(v___x_2825_, v_configKey_2823_);
v_h_2827_ = lean_uint64_to_usize(v___x_2826_);
v___x_2828_ = ((size_t)5ULL);
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = ((size_t)1ULL);
v___x_2831_ = lean_usize_sub(v_depth_2814_, v___x_2830_);
v___x_2832_ = lean_usize_mul(v___x_2828_, v___x_2831_);
v_h_2833_ = lean_usize_shift_right(v_h_2827_, v___x_2832_);
v___x_2834_ = lean_nat_add(v_i_2817_, v___x_2829_);
lean_dec(v_i_2817_);
lean_inc(v_v_2824_);
lean_inc(v_k_2821_);
v___x_2835_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_entries_2818_, v_h_2833_, v_depth_2814_, v_k_2821_, v_v_2824_);
v_i_2817_ = v___x_2834_;
v_entries_2818_ = v___x_2835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_2837_, lean_object* v_keys_2838_, lean_object* v_vals_2839_, lean_object* v_i_2840_, lean_object* v_entries_2841_){
_start:
{
size_t v_depth_boxed_2842_; lean_object* v_res_2843_; 
v_depth_boxed_2842_ = lean_unbox_usize(v_depth_2837_);
lean_dec(v_depth_2837_);
v_res_2843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2842_, v_keys_2838_, v_vals_2839_, v_i_2840_, v_entries_2841_);
lean_dec_ref(v_vals_2839_);
lean_dec_ref(v_keys_2838_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg___boxed(lean_object* v_x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_, lean_object* v_x_2848_){
_start:
{
size_t v_x_2171__boxed_2849_; size_t v_x_2172__boxed_2850_; lean_object* v_res_2851_; 
v_x_2171__boxed_2849_ = lean_unbox_usize(v_x_2845_);
lean_dec(v_x_2845_);
v_x_2172__boxed_2850_ = lean_unbox_usize(v_x_2846_);
lean_dec(v_x_2846_);
v_res_2851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2844_, v_x_2171__boxed_2849_, v_x_2172__boxed_2850_, v_x_2847_, v_x_2848_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* v_x_2852_, lean_object* v_x_2853_, lean_object* v_x_2854_){
_start:
{
lean_object* v_expr_2855_; uint64_t v_configKey_2856_; uint64_t v___x_2857_; uint64_t v___x_2858_; size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v_expr_2855_ = lean_ctor_get(v_x_2853_, 0);
v_configKey_2856_ = lean_ctor_get_uint64(v_x_2853_, sizeof(void*)*1);
v___x_2857_ = l_Lean_Expr_hash(v_expr_2855_);
v___x_2858_ = lean_uint64_mix_hash(v___x_2857_, v_configKey_2856_);
v___x_2859_ = lean_uint64_to_usize(v___x_2858_);
v___x_2860_ = ((size_t)1ULL);
v___x_2861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_2852_, v___x_2859_, v___x_2860_, v_x_2853_, v_x_2854_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2862_, lean_object* v_vals_2863_, lean_object* v_i_2864_, lean_object* v_k_2865_){
_start:
{
uint8_t v___y_2867_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = lean_array_get_size(v_keys_2862_);
v___x_2874_ = lean_nat_dec_lt(v_i_2864_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_dec(v_i_2864_);
v___x_2875_ = lean_box(0);
return v___x_2875_;
}
else
{
lean_object* v_expr_2876_; uint64_t v_configKey_2877_; lean_object* v_k_x27_2878_; lean_object* v_expr_2879_; uint64_t v_configKey_2880_; uint8_t v___x_2881_; 
v_expr_2876_ = lean_ctor_get(v_k_2865_, 0);
v_configKey_2877_ = lean_ctor_get_uint64(v_k_2865_, sizeof(void*)*1);
v_k_x27_2878_ = lean_array_fget_borrowed(v_keys_2862_, v_i_2864_);
v_expr_2879_ = lean_ctor_get(v_k_x27_2878_, 0);
v_configKey_2880_ = lean_ctor_get_uint64(v_k_x27_2878_, sizeof(void*)*1);
v___x_2881_ = lean_expr_equal(v_expr_2876_, v_expr_2879_);
if (v___x_2881_ == 0)
{
v___y_2867_ = v___x_2881_;
goto v___jp_2866_;
}
else
{
uint8_t v___x_2882_; 
v___x_2882_ = lean_uint64_dec_eq(v_configKey_2877_, v_configKey_2880_);
v___y_2867_ = v___x_2882_;
goto v___jp_2866_;
}
}
v___jp_2866_:
{
if (v___y_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_add(v_i_2864_, v___x_2868_);
lean_dec(v_i_2864_);
v_i_2864_ = v___x_2869_;
goto _start;
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_array_fget_borrowed(v_vals_2863_, v_i_2864_);
lean_dec(v_i_2864_);
lean_inc(v___x_2871_);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2883_, lean_object* v_vals_2884_, lean_object* v_i_2885_, lean_object* v_k_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_2883_, v_vals_2884_, v_i_2885_, v_k_2886_);
lean_dec_ref(v_k_2886_);
lean_dec_ref(v_vals_2884_);
lean_dec_ref(v_keys_2883_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(lean_object* v_x_2888_, size_t v_x_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2888_) == 0)
{
lean_object* v_es_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2919_; 
v_es_2891_ = lean_ctor_get(v_x_2888_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_x_2888_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2893_ = v_x_2888_;
v_isShared_2894_ = v_isSharedCheck_2919_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_es_2891_);
lean_dec(v_x_2888_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2919_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; size_t v___x_2896_; size_t v___x_2897_; size_t v___x_2898_; lean_object* v_j_2899_; lean_object* v___x_2900_; 
v___x_2895_ = lean_box(2);
v___x_2896_ = ((size_t)5ULL);
v___x_2897_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_getLevel_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2898_ = lean_usize_land(v_x_2889_, v___x_2897_);
v_j_2899_ = lean_usize_to_nat(v___x_2898_);
v___x_2900_ = lean_array_get(v___x_2895_, v_es_2891_, v_j_2899_);
lean_dec(v_j_2899_);
lean_dec_ref(v_es_2891_);
switch(lean_obj_tag(v___x_2900_))
{
case 0:
{
lean_object* v_key_2901_; lean_object* v_val_2902_; uint8_t v___y_2904_; lean_object* v_expr_2909_; uint64_t v_configKey_2910_; lean_object* v_expr_2911_; uint64_t v_configKey_2912_; uint8_t v___x_2913_; 
v_key_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_key_2901_);
v_val_2902_ = lean_ctor_get(v___x_2900_, 1);
lean_inc(v_val_2902_);
lean_dec_ref(v___x_2900_);
v_expr_2909_ = lean_ctor_get(v_x_2890_, 0);
v_configKey_2910_ = lean_ctor_get_uint64(v_x_2890_, sizeof(void*)*1);
v_expr_2911_ = lean_ctor_get(v_key_2901_, 0);
lean_inc_ref(v_expr_2911_);
v_configKey_2912_ = lean_ctor_get_uint64(v_key_2901_, sizeof(void*)*1);
lean_dec(v_key_2901_);
v___x_2913_ = lean_expr_equal(v_expr_2909_, v_expr_2911_);
lean_dec_ref(v_expr_2911_);
if (v___x_2913_ == 0)
{
v___y_2904_ = v___x_2913_;
goto v___jp_2903_;
}
else
{
uint8_t v___x_2914_; 
v___x_2914_ = lean_uint64_dec_eq(v_configKey_2910_, v_configKey_2912_);
v___y_2904_ = v___x_2914_;
goto v___jp_2903_;
}
v___jp_2903_:
{
if (v___y_2904_ == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_val_2902_);
lean_del_object(v___x_2893_);
v___x_2905_ = lean_box(0);
return v___x_2905_;
}
else
{
lean_object* v___x_2907_; 
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 1);
lean_ctor_set(v___x_2893_, 0, v_val_2902_);
v___x_2907_ = v___x_2893_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_val_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
case 1:
{
lean_object* v_node_2915_; size_t v___x_2916_; 
lean_del_object(v___x_2893_);
v_node_2915_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_node_2915_);
lean_dec_ref(v___x_2900_);
v___x_2916_ = lean_usize_shift_right(v_x_2889_, v___x_2896_);
v_x_2888_ = v_node_2915_;
v_x_2889_ = v___x_2916_;
goto _start;
}
default: 
{
lean_object* v___x_2918_; 
lean_del_object(v___x_2893_);
v___x_2918_ = lean_box(0);
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_ks_2920_; lean_object* v_vs_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_ks_2920_ = lean_ctor_get(v_x_2888_, 0);
lean_inc_ref(v_ks_2920_);
v_vs_2921_ = lean_ctor_get(v_x_2888_, 1);
lean_inc_ref(v_vs_2921_);
lean_dec_ref(v_x_2888_);
v___x_2922_ = lean_unsigned_to_nat(0u);
v___x_2923_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_ks_2920_, v_vs_2921_, v___x_2922_, v_x_2890_);
lean_dec_ref(v_vs_2921_);
lean_dec_ref(v_ks_2920_);
return v___x_2923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg___boxed(lean_object* v_x_2924_, lean_object* v_x_2925_, lean_object* v_x_2926_){
_start:
{
size_t v_x_2386__boxed_2927_; lean_object* v_res_2928_; 
v_x_2386__boxed_2927_ = lean_unbox_usize(v_x_2925_);
lean_dec(v_x_2925_);
v_res_2928_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2924_, v_x_2386__boxed_2927_, v_x_2926_);
lean_dec_ref(v_x_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
lean_object* v_expr_2931_; uint64_t v_configKey_2932_; uint64_t v___x_2933_; uint64_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v_expr_2931_ = lean_ctor_get(v_x_2930_, 0);
v_configKey_2932_ = lean_ctor_get_uint64(v_x_2930_, sizeof(void*)*1);
v___x_2933_ = l_Lean_Expr_hash(v_expr_2931_);
v___x_2934_ = lean_uint64_mix_hash(v___x_2933_, v_configKey_2932_);
v___x_2935_ = lean_uint64_to_usize(v___x_2934_);
v___x_2936_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_2929_, v___x_2935_, v_x_2930_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg___boxed(lean_object* v_x_2937_, lean_object* v_x_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_2937_, v_x_2938_);
lean_dec_ref(v_x_2938_);
return v_res_2939_;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__0));
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(lean_object* v_e_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
switch(lean_obj_tag(v_e_2943_))
{
case 0:
{
lean_object* v_deBruijnIndex_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_deBruijnIndex_2949_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_deBruijnIndex_2949_);
lean_dec_ref(v_e_2943_);
v___x_2950_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___closed__1);
v___x_2951_ = l_Lean_mkBVar(v_deBruijnIndex_2949_);
v___x_2952_ = l_Lean_MessageData_ofExpr(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2950_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_2953_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
return v___x_2954_;
}
case 1:
{
lean_object* v_fvarId_2955_; lean_object* v___x_2956_; 
lean_dec(v_a_2945_);
v_fvarId_2955_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_fvarId_2955_);
lean_dec_ref(v_e_2943_);
v___x_2956_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_2955_, v_a_2944_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
return v___x_2956_;
}
case 2:
{
lean_object* v_mvarId_2957_; lean_object* v___x_2958_; 
v_mvarId_2957_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_mvarId_2957_);
lean_dec_ref(v_e_2943_);
v___x_2958_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_2957_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
return v___x_2958_;
}
case 3:
{
lean_object* v_u_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_u_2959_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_u_2959_);
lean_dec_ref(v_e_2943_);
v___x_2960_ = l_Lean_Level_succ___override(v_u_2959_);
v___x_2961_ = l_Lean_mkSort(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
case 4:
{
lean_object* v_us_2963_; 
v_us_2963_ = lean_ctor_get(v_e_2943_, 1);
lean_inc(v_us_2963_);
if (lean_obj_tag(v_us_2963_) == 0)
{
lean_object* v_declName_2964_; lean_object* v___x_2965_; 
v_declName_2964_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_declName_2964_);
lean_dec_ref(v_e_2943_);
v___x_2965_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2964_, v_us_2963_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
return v___x_2965_;
}
else
{
uint8_t v_cacheInferType_2966_; 
v_cacheInferType_2966_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*7 + 3);
if (v_cacheInferType_2966_ == 0)
{
lean_object* v_declName_2967_; lean_object* v___x_2968_; 
v_declName_2967_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_declName_2967_);
lean_dec_ref(v_e_2943_);
v___x_2968_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2967_, v_us_2963_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
return v___x_2968_;
}
else
{
lean_object* v_declName_2969_; uint8_t v___x_2970_; 
v_declName_2969_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_declName_2969_);
v___x_2970_ = l_Lean_Expr_hasMVar(v_e_2943_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2943_, v_a_2944_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3023_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_3023_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3023_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v_cache_2977_; lean_object* v_inferType_2978_; lean_object* v___x_2979_; 
v___x_2976_ = lean_st_ref_get(v_a_2945_);
v_cache_2977_ = lean_ctor_get(v___x_2976_, 1);
lean_inc_ref(v_cache_2977_);
lean_dec(v___x_2976_);
v_inferType_2978_ = lean_ctor_get(v_cache_2977_, 0);
lean_inc_ref(v_inferType_2978_);
lean_dec_ref(v_cache_2977_);
v___x_2979_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_2978_, v_a_2972_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2980_; 
lean_del_object(v___x_2974_);
v___x_2980_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2969_, v_us_2963_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2944_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; uint8_t v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
v___x_2982_ = l_Lean_Expr_hasMVar(v_a_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3017_; 
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3017_ == 0)
{
lean_object* v_unused_3018_; 
v_unused_3018_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_3018_);
v___x_2984_ = v___x_2980_;
v_isShared_2985_ = v_isSharedCheck_3017_;
goto v_resetjp_2983_;
}
else
{
lean_dec(v___x_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3017_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v_cache_2987_; lean_object* v_mctx_2988_; lean_object* v_zetaDeltaFVarIds_2989_; lean_object* v_postponed_2990_; lean_object* v_diag_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3016_; 
v___x_2986_ = lean_st_ref_take(v_a_2945_);
v_cache_2987_ = lean_ctor_get(v___x_2986_, 1);
v_mctx_2988_ = lean_ctor_get(v___x_2986_, 0);
v_zetaDeltaFVarIds_2989_ = lean_ctor_get(v___x_2986_, 2);
v_postponed_2990_ = lean_ctor_get(v___x_2986_, 3);
v_diag_2991_ = lean_ctor_get(v___x_2986_, 4);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2993_ = v___x_2986_;
v_isShared_2994_ = v_isSharedCheck_3016_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_diag_2991_);
lean_inc(v_postponed_2990_);
lean_inc(v_zetaDeltaFVarIds_2989_);
lean_inc(v_cache_2987_);
lean_inc(v_mctx_2988_);
lean_dec(v___x_2986_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3016_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v_inferType_2995_; lean_object* v_funInfo_2996_; lean_object* v_synthInstance_2997_; lean_object* v_whnf_2998_; lean_object* v_defEqTrans_2999_; lean_object* v_defEqPerm_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3015_; 
v_inferType_2995_ = lean_ctor_get(v_cache_2987_, 0);
v_funInfo_2996_ = lean_ctor_get(v_cache_2987_, 1);
v_synthInstance_2997_ = lean_ctor_get(v_cache_2987_, 2);
v_whnf_2998_ = lean_ctor_get(v_cache_2987_, 3);
v_defEqTrans_2999_ = lean_ctor_get(v_cache_2987_, 4);
v_defEqPerm_3000_ = lean_ctor_get(v_cache_2987_, 5);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_cache_2987_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3002_ = v_cache_2987_;
v_isShared_3003_ = v_isSharedCheck_3015_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_defEqPerm_3000_);
lean_inc(v_defEqTrans_2999_);
lean_inc(v_whnf_2998_);
lean_inc(v_synthInstance_2997_);
lean_inc(v_funInfo_2996_);
lean_inc(v_inferType_2995_);
lean_dec(v_cache_2987_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3015_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
lean_inc(v_a_2981_);
v___x_3004_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_2995_, v_a_2972_, v_a_2981_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3004_);
v___x_3006_ = v___x_3002_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_funInfo_2996_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_synthInstance_2997_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_whnf_2998_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v_defEqTrans_2999_);
lean_ctor_set(v_reuseFailAlloc_3014_, 5, v_defEqPerm_3000_);
v___x_3006_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3008_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v___x_3006_);
v___x_3008_ = v___x_2993_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_mctx_2988_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_zetaDeltaFVarIds_2989_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_postponed_2990_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_diag_2991_);
v___x_3008_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3009_ = lean_st_ref_set(v_a_2945_, v___x_3008_);
lean_dec(v_a_2945_);
if (v_isShared_2985_ == 0)
{
v___x_3011_ = v___x_2984_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_2981_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2981_);
lean_dec(v_a_2972_);
lean_dec(v_a_2945_);
return v___x_2980_;
}
}
else
{
lean_dec(v_a_2972_);
lean_dec(v_a_2945_);
return v___x_2980_;
}
}
else
{
lean_object* v_val_3019_; lean_object* v___x_3021_; 
lean_dec(v_a_2972_);
lean_dec(v_declName_2969_);
lean_dec(v_us_2963_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_val_3019_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_val_3019_);
lean_dec_ref(v___x_2979_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v_val_3019_);
v___x_3021_ = v___x_2974_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_val_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v_declName_2969_);
lean_dec(v_us_2963_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_a_3024_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2971_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2971_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v___x_3032_; 
lean_dec_ref(v_e_2943_);
v___x_3032_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_2969_, v_us_2963_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
return v___x_3032_;
}
}
}
}
case 5:
{
lean_object* v_fn_3033_; uint8_t v_cacheInferType_3034_; lean_object* v_nargs_3035_; lean_object* v___x_3036_; lean_object* v_dummy_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_fn_3033_ = lean_ctor_get(v_e_2943_, 0);
v_cacheInferType_3034_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*7 + 3);
v_nargs_3035_ = l_Lean_Expr_getAppNumArgs(v_e_2943_);
v___x_3036_ = l_Lean_Expr_getAppFn(v_fn_3033_);
v_dummy_3037_ = lean_obj_once(&l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0, &l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0_once, _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
lean_inc(v_nargs_3035_);
v___x_3038_ = lean_mk_array(v_nargs_3035_, v_dummy_3037_);
v___x_3039_ = lean_unsigned_to_nat(1u);
v___x_3040_ = lean_nat_sub(v_nargs_3035_, v___x_3039_);
lean_dec(v_nargs_3035_);
lean_inc_ref(v_e_2943_);
v___x_3041_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2943_, v___x_3038_, v___x_3040_);
if (v_cacheInferType_3034_ == 0)
{
lean_object* v___x_3042_; 
lean_dec_ref(v_e_2943_);
v___x_3042_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3036_, v___x_3041_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec_ref(v___x_3041_);
return v___x_3042_;
}
else
{
uint8_t v___x_3043_; 
v___x_3043_ = l_Lean_Expr_hasMVar(v_e_2943_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2943_, v_a_2944_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3096_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3096_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3096_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v_cache_3050_; lean_object* v_inferType_3051_; lean_object* v___x_3052_; 
v___x_3049_ = lean_st_ref_get(v_a_2945_);
v_cache_3050_ = lean_ctor_get(v___x_3049_, 1);
lean_inc_ref(v_cache_3050_);
lean_dec(v___x_3049_);
v_inferType_3051_ = lean_ctor_get(v_cache_3050_, 0);
lean_inc_ref(v_inferType_3051_);
lean_dec_ref(v_cache_3050_);
v___x_3052_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3051_, v_a_3045_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3053_; 
lean_del_object(v___x_3047_);
lean_inc(v_a_2945_);
v___x_3053_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3036_, v___x_3041_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec_ref(v___x_3041_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; uint8_t v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
v___x_3055_ = l_Lean_Expr_hasMVar(v_a_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3090_; 
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3053_, 0);
lean_dec(v_unused_3091_);
v___x_3057_ = v___x_3053_;
v_isShared_3058_ = v_isSharedCheck_3090_;
goto v_resetjp_3056_;
}
else
{
lean_dec(v___x_3053_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3090_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v_cache_3060_; lean_object* v_mctx_3061_; lean_object* v_zetaDeltaFVarIds_3062_; lean_object* v_postponed_3063_; lean_object* v_diag_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3089_; 
v___x_3059_ = lean_st_ref_take(v_a_2945_);
v_cache_3060_ = lean_ctor_get(v___x_3059_, 1);
v_mctx_3061_ = lean_ctor_get(v___x_3059_, 0);
v_zetaDeltaFVarIds_3062_ = lean_ctor_get(v___x_3059_, 2);
v_postponed_3063_ = lean_ctor_get(v___x_3059_, 3);
v_diag_3064_ = lean_ctor_get(v___x_3059_, 4);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3066_ = v___x_3059_;
v_isShared_3067_ = v_isSharedCheck_3089_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_diag_3064_);
lean_inc(v_postponed_3063_);
lean_inc(v_zetaDeltaFVarIds_3062_);
lean_inc(v_cache_3060_);
lean_inc(v_mctx_3061_);
lean_dec(v___x_3059_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3089_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v_inferType_3068_; lean_object* v_funInfo_3069_; lean_object* v_synthInstance_3070_; lean_object* v_whnf_3071_; lean_object* v_defEqTrans_3072_; lean_object* v_defEqPerm_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3088_; 
v_inferType_3068_ = lean_ctor_get(v_cache_3060_, 0);
v_funInfo_3069_ = lean_ctor_get(v_cache_3060_, 1);
v_synthInstance_3070_ = lean_ctor_get(v_cache_3060_, 2);
v_whnf_3071_ = lean_ctor_get(v_cache_3060_, 3);
v_defEqTrans_3072_ = lean_ctor_get(v_cache_3060_, 4);
v_defEqPerm_3073_ = lean_ctor_get(v_cache_3060_, 5);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_cache_3060_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3075_ = v_cache_3060_;
v_isShared_3076_ = v_isSharedCheck_3088_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_defEqPerm_3073_);
lean_inc(v_defEqTrans_3072_);
lean_inc(v_whnf_3071_);
lean_inc(v_synthInstance_3070_);
lean_inc(v_funInfo_3069_);
lean_inc(v_inferType_3068_);
lean_dec(v_cache_3060_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3088_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
lean_inc(v_a_3054_);
v___x_3077_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3068_, v_a_3045_, v_a_3054_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3077_);
v___x_3079_ = v___x_3075_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_funInfo_3069_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_synthInstance_3070_);
lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_whnf_3071_);
lean_ctor_set(v_reuseFailAlloc_3087_, 4, v_defEqTrans_3072_);
lean_ctor_set(v_reuseFailAlloc_3087_, 5, v_defEqPerm_3073_);
v___x_3079_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3081_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___x_3079_);
v___x_3081_ = v___x_3066_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_mctx_3061_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_zetaDeltaFVarIds_3062_);
lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_postponed_3063_);
lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_diag_3064_);
v___x_3081_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = lean_st_ref_set(v_a_2945_, v___x_3081_);
lean_dec(v_a_2945_);
if (v_isShared_3058_ == 0)
{
v___x_3084_ = v___x_3057_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3054_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3054_);
lean_dec(v_a_3045_);
lean_dec(v_a_2945_);
return v___x_3053_;
}
}
else
{
lean_dec(v_a_3045_);
lean_dec(v_a_2945_);
return v___x_3053_;
}
}
else
{
lean_object* v_val_3092_; lean_object* v___x_3094_; 
lean_dec(v_a_3045_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v___x_3036_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_val_3092_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_val_3092_);
lean_dec_ref(v___x_3052_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v_val_3092_);
v___x_3094_ = v___x_3047_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_val_3092_);
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
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v___x_3041_);
lean_dec_ref(v___x_3036_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_a_3097_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3044_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3044_);
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
lean_dec_ref(v_e_2943_);
v___x_3105_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(v___x_3036_, v___x_3041_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec_ref(v___x_3041_);
return v___x_3105_;
}
}
}
case 7:
{
uint8_t v_cacheInferType_3106_; 
v_cacheInferType_3106_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3106_ == 0)
{
lean_object* v___x_3107_; 
v___x_3107_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3107_;
}
else
{
uint8_t v___x_3108_; 
v___x_3108_ = l_Lean_Expr_hasMVar(v_e_2943_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_inc_ref(v_e_2943_);
v___x_3109_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2943_, v_a_2944_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3161_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3161_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3161_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v_cache_3115_; lean_object* v_inferType_3116_; lean_object* v___x_3117_; 
v___x_3114_ = lean_st_ref_get(v_a_2945_);
v_cache_3115_ = lean_ctor_get(v___x_3114_, 1);
lean_inc_ref(v_cache_3115_);
lean_dec(v___x_3114_);
v_inferType_3116_ = lean_ctor_get(v_cache_3115_, 0);
lean_inc_ref(v_inferType_3116_);
lean_dec_ref(v_cache_3115_);
v___x_3117_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3116_, v_a_3110_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v___x_3118_; 
lean_del_object(v___x_3112_);
lean_inc(v_a_2945_);
v___x_3118_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; uint8_t v___x_3120_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
v___x_3120_ = l_Lean_Expr_hasMVar(v_a_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3155_; 
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; 
v_unused_3156_ = lean_ctor_get(v___x_3118_, 0);
lean_dec(v_unused_3156_);
v___x_3122_ = v___x_3118_;
v_isShared_3123_ = v_isSharedCheck_3155_;
goto v_resetjp_3121_;
}
else
{
lean_dec(v___x_3118_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3155_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v_cache_3125_; lean_object* v_mctx_3126_; lean_object* v_zetaDeltaFVarIds_3127_; lean_object* v_postponed_3128_; lean_object* v_diag_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3154_; 
v___x_3124_ = lean_st_ref_take(v_a_2945_);
v_cache_3125_ = lean_ctor_get(v___x_3124_, 1);
v_mctx_3126_ = lean_ctor_get(v___x_3124_, 0);
v_zetaDeltaFVarIds_3127_ = lean_ctor_get(v___x_3124_, 2);
v_postponed_3128_ = lean_ctor_get(v___x_3124_, 3);
v_diag_3129_ = lean_ctor_get(v___x_3124_, 4);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3131_ = v___x_3124_;
v_isShared_3132_ = v_isSharedCheck_3154_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_diag_3129_);
lean_inc(v_postponed_3128_);
lean_inc(v_zetaDeltaFVarIds_3127_);
lean_inc(v_cache_3125_);
lean_inc(v_mctx_3126_);
lean_dec(v___x_3124_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3154_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v_inferType_3133_; lean_object* v_funInfo_3134_; lean_object* v_synthInstance_3135_; lean_object* v_whnf_3136_; lean_object* v_defEqTrans_3137_; lean_object* v_defEqPerm_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3153_; 
v_inferType_3133_ = lean_ctor_get(v_cache_3125_, 0);
v_funInfo_3134_ = lean_ctor_get(v_cache_3125_, 1);
v_synthInstance_3135_ = lean_ctor_get(v_cache_3125_, 2);
v_whnf_3136_ = lean_ctor_get(v_cache_3125_, 3);
v_defEqTrans_3137_ = lean_ctor_get(v_cache_3125_, 4);
v_defEqPerm_3138_ = lean_ctor_get(v_cache_3125_, 5);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_cache_3125_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3140_ = v_cache_3125_;
v_isShared_3141_ = v_isSharedCheck_3153_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_defEqPerm_3138_);
lean_inc(v_defEqTrans_3137_);
lean_inc(v_whnf_3136_);
lean_inc(v_synthInstance_3135_);
lean_inc(v_funInfo_3134_);
lean_inc(v_inferType_3133_);
lean_dec(v_cache_3125_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3153_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_inc(v_a_3119_);
v___x_3142_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3133_, v_a_3110_, v_a_3119_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_funInfo_3134_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v_synthInstance_3135_);
lean_ctor_set(v_reuseFailAlloc_3152_, 3, v_whnf_3136_);
lean_ctor_set(v_reuseFailAlloc_3152_, 4, v_defEqTrans_3137_);
lean_ctor_set(v_reuseFailAlloc_3152_, 5, v_defEqPerm_3138_);
v___x_3144_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3146_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 1, v___x_3144_);
v___x_3146_ = v___x_3131_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_mctx_3126_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_zetaDeltaFVarIds_3127_);
lean_ctor_set(v_reuseFailAlloc_3151_, 3, v_postponed_3128_);
lean_ctor_set(v_reuseFailAlloc_3151_, 4, v_diag_3129_);
v___x_3146_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = lean_st_ref_set(v_a_2945_, v___x_3146_);
lean_dec(v_a_2945_);
if (v_isShared_3123_ == 0)
{
v___x_3149_ = v___x_3122_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3119_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3119_);
lean_dec(v_a_3110_);
lean_dec(v_a_2945_);
return v___x_3118_;
}
}
else
{
lean_dec(v_a_3110_);
lean_dec(v_a_2945_);
return v___x_3118_;
}
}
else
{
lean_object* v_val_3157_; lean_object* v___x_3159_; 
lean_dec(v_a_3110_);
lean_dec_ref(v_e_2943_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_val_3157_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_val_3157_);
lean_dec_ref(v___x_3117_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v_val_3157_);
v___x_3159_ = v___x_3112_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_val_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v_e_2943_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_a_3162_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3109_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3109_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_object* v___x_3170_; 
v___x_3170_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(v_e_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3170_;
}
}
}
case 9:
{
lean_object* v_a_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_a_3171_ = lean_ctor_get(v_e_2943_, 0);
lean_inc_ref(v_a_3171_);
lean_dec_ref(v_e_2943_);
v___x_3172_ = l_Lean_Literal_type(v_a_3171_);
lean_dec_ref(v_a_3171_);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
case 10:
{
lean_object* v_expr_3174_; 
v_expr_3174_ = lean_ctor_get(v_e_2943_, 1);
lean_inc_ref(v_expr_3174_);
lean_dec_ref(v_e_2943_);
v_e_2943_ = v_expr_3174_;
goto _start;
}
case 11:
{
uint8_t v_cacheInferType_3176_; 
v_cacheInferType_3176_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3176_ == 0)
{
lean_object* v_typeName_3177_; lean_object* v_idx_3178_; lean_object* v_struct_3179_; lean_object* v___x_3180_; 
v_typeName_3177_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_typeName_3177_);
v_idx_3178_ = lean_ctor_get(v_e_2943_, 1);
lean_inc(v_idx_3178_);
v_struct_3179_ = lean_ctor_get(v_e_2943_, 2);
lean_inc_ref(v_struct_3179_);
lean_dec_ref(v_e_2943_);
v___x_3180_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3177_, v_idx_3178_, v_struct_3179_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3180_;
}
else
{
lean_object* v_typeName_3181_; lean_object* v_idx_3182_; lean_object* v_struct_3183_; uint8_t v___x_3184_; 
v_typeName_3181_ = lean_ctor_get(v_e_2943_, 0);
lean_inc(v_typeName_3181_);
v_idx_3182_ = lean_ctor_get(v_e_2943_, 1);
lean_inc(v_idx_3182_);
v_struct_3183_ = lean_ctor_get(v_e_2943_, 2);
lean_inc_ref(v_struct_3183_);
v___x_3184_ = l_Lean_Expr_hasMVar(v_e_2943_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2943_, v_a_2944_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3237_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3188_ = v___x_3185_;
v_isShared_3189_ = v_isSharedCheck_3237_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3237_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v_cache_3191_; lean_object* v_inferType_3192_; lean_object* v___x_3193_; 
v___x_3190_ = lean_st_ref_get(v_a_2945_);
v_cache_3191_ = lean_ctor_get(v___x_3190_, 1);
lean_inc_ref(v_cache_3191_);
lean_dec(v___x_3190_);
v_inferType_3192_ = lean_ctor_get(v_cache_3191_, 0);
lean_inc_ref(v_inferType_3192_);
lean_dec_ref(v_cache_3191_);
v___x_3193_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3192_, v_a_3186_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v___x_3194_; 
lean_del_object(v___x_3188_);
lean_inc(v_a_2945_);
v___x_3194_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3181_, v_idx_3182_, v_struct_3183_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; uint8_t v___x_3196_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
v___x_3196_ = l_Lean_Expr_hasMVar(v_a_3195_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3231_; 
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v___x_3194_, 0);
lean_dec(v_unused_3232_);
v___x_3198_ = v___x_3194_;
v_isShared_3199_ = v_isSharedCheck_3231_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v___x_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3231_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v_cache_3201_; lean_object* v_mctx_3202_; lean_object* v_zetaDeltaFVarIds_3203_; lean_object* v_postponed_3204_; lean_object* v_diag_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3230_; 
v___x_3200_ = lean_st_ref_take(v_a_2945_);
v_cache_3201_ = lean_ctor_get(v___x_3200_, 1);
v_mctx_3202_ = lean_ctor_get(v___x_3200_, 0);
v_zetaDeltaFVarIds_3203_ = lean_ctor_get(v___x_3200_, 2);
v_postponed_3204_ = lean_ctor_get(v___x_3200_, 3);
v_diag_3205_ = lean_ctor_get(v___x_3200_, 4);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3207_ = v___x_3200_;
v_isShared_3208_ = v_isSharedCheck_3230_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_diag_3205_);
lean_inc(v_postponed_3204_);
lean_inc(v_zetaDeltaFVarIds_3203_);
lean_inc(v_cache_3201_);
lean_inc(v_mctx_3202_);
lean_dec(v___x_3200_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3230_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_inferType_3209_; lean_object* v_funInfo_3210_; lean_object* v_synthInstance_3211_; lean_object* v_whnf_3212_; lean_object* v_defEqTrans_3213_; lean_object* v_defEqPerm_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3229_; 
v_inferType_3209_ = lean_ctor_get(v_cache_3201_, 0);
v_funInfo_3210_ = lean_ctor_get(v_cache_3201_, 1);
v_synthInstance_3211_ = lean_ctor_get(v_cache_3201_, 2);
v_whnf_3212_ = lean_ctor_get(v_cache_3201_, 3);
v_defEqTrans_3213_ = lean_ctor_get(v_cache_3201_, 4);
v_defEqPerm_3214_ = lean_ctor_get(v_cache_3201_, 5);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_cache_3201_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3216_ = v_cache_3201_;
v_isShared_3217_ = v_isSharedCheck_3229_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_defEqPerm_3214_);
lean_inc(v_defEqTrans_3213_);
lean_inc(v_whnf_3212_);
lean_inc(v_synthInstance_3211_);
lean_inc(v_funInfo_3210_);
lean_inc(v_inferType_3209_);
lean_dec(v_cache_3201_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3229_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
lean_inc(v_a_3195_);
v___x_3218_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3209_, v_a_3186_, v_a_3195_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3218_);
v___x_3220_ = v___x_3216_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_funInfo_3210_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_synthInstance_3211_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_whnf_3212_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_defEqTrans_3213_);
lean_ctor_set(v_reuseFailAlloc_3228_, 5, v_defEqPerm_3214_);
v___x_3220_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3220_);
v___x_3222_ = v___x_3207_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_mctx_3202_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_zetaDeltaFVarIds_3203_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_postponed_3204_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_diag_3205_);
v___x_3222_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_st_ref_set(v_a_2945_, v___x_3222_);
lean_dec(v_a_2945_);
if (v_isShared_3199_ == 0)
{
v___x_3225_ = v___x_3198_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3195_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3195_);
lean_dec(v_a_3186_);
lean_dec(v_a_2945_);
return v___x_3194_;
}
}
else
{
lean_dec(v_a_3186_);
lean_dec(v_a_2945_);
return v___x_3194_;
}
}
else
{
lean_object* v_val_3233_; lean_object* v___x_3235_; 
lean_dec(v_a_3186_);
lean_dec_ref(v_struct_3183_);
lean_dec(v_idx_3182_);
lean_dec(v_typeName_3181_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_val_3233_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_val_3233_);
lean_dec_ref(v___x_3193_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v_val_3233_);
v___x_3235_ = v___x_3188_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_val_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v_struct_3183_);
lean_dec(v_idx_3182_);
lean_dec(v_typeName_3181_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
v_a_3238_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3185_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3185_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
else
{
lean_object* v___x_3246_; 
lean_dec_ref(v_e_2943_);
v___x_3246_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(v_typeName_3181_, v_idx_3182_, v_struct_3183_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3246_;
}
}
}
default: 
{
uint8_t v_cacheInferType_3247_; 
v_cacheInferType_3247_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*7 + 3);
if (v_cacheInferType_3247_ == 0)
{
lean_object* v___x_3248_; 
v___x_3248_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3248_;
}
else
{
uint8_t v___x_3249_; 
v___x_3249_ = l_Lean_Expr_hasMVar(v_e_2943_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
lean_inc_ref(v_e_2943_);
v___x_3250_ = l_Lean_Meta_mkExprConfigCacheKey___redArg(v_e_2943_, v_a_2944_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3302_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3302_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3302_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v_cache_3256_; lean_object* v_inferType_3257_; lean_object* v___x_3258_; 
v___x_3255_ = lean_st_ref_get(v_a_2945_);
v_cache_3256_ = lean_ctor_get(v___x_3255_, 1);
lean_inc_ref(v_cache_3256_);
lean_dec(v___x_3255_);
v_inferType_3257_ = lean_ctor_get(v_cache_3256_, 0);
lean_inc_ref(v_inferType_3257_);
lean_dec_ref(v_cache_3256_);
v___x_3258_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_inferType_3257_, v_a_3251_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v___x_3259_; 
lean_del_object(v___x_3253_);
lean_inc(v_a_2945_);
v___x_3259_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; uint8_t v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
v___x_3261_ = l_Lean_Expr_hasMVar(v_a_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3296_; 
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; 
v_unused_3297_ = lean_ctor_get(v___x_3259_, 0);
lean_dec(v_unused_3297_);
v___x_3263_ = v___x_3259_;
v_isShared_3264_ = v_isSharedCheck_3296_;
goto v_resetjp_3262_;
}
else
{
lean_dec(v___x_3259_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3296_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v_cache_3266_; lean_object* v_mctx_3267_; lean_object* v_zetaDeltaFVarIds_3268_; lean_object* v_postponed_3269_; lean_object* v_diag_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3295_; 
v___x_3265_ = lean_st_ref_take(v_a_2945_);
v_cache_3266_ = lean_ctor_get(v___x_3265_, 1);
v_mctx_3267_ = lean_ctor_get(v___x_3265_, 0);
v_zetaDeltaFVarIds_3268_ = lean_ctor_get(v___x_3265_, 2);
v_postponed_3269_ = lean_ctor_get(v___x_3265_, 3);
v_diag_3270_ = lean_ctor_get(v___x_3265_, 4);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3272_ = v___x_3265_;
v_isShared_3273_ = v_isSharedCheck_3295_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_diag_3270_);
lean_inc(v_postponed_3269_);
lean_inc(v_zetaDeltaFVarIds_3268_);
lean_inc(v_cache_3266_);
lean_inc(v_mctx_3267_);
lean_dec(v___x_3265_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3295_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v_inferType_3274_; lean_object* v_funInfo_3275_; lean_object* v_synthInstance_3276_; lean_object* v_whnf_3277_; lean_object* v_defEqTrans_3278_; lean_object* v_defEqPerm_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3294_; 
v_inferType_3274_ = lean_ctor_get(v_cache_3266_, 0);
v_funInfo_3275_ = lean_ctor_get(v_cache_3266_, 1);
v_synthInstance_3276_ = lean_ctor_get(v_cache_3266_, 2);
v_whnf_3277_ = lean_ctor_get(v_cache_3266_, 3);
v_defEqTrans_3278_ = lean_ctor_get(v_cache_3266_, 4);
v_defEqPerm_3279_ = lean_ctor_get(v_cache_3266_, 5);
v_isSharedCheck_3294_ = !lean_is_exclusive(v_cache_3266_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3281_ = v_cache_3266_;
v_isShared_3282_ = v_isSharedCheck_3294_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_defEqPerm_3279_);
lean_inc(v_defEqTrans_3278_);
lean_inc(v_whnf_3277_);
lean_inc(v_synthInstance_3276_);
lean_inc(v_funInfo_3275_);
lean_inc(v_inferType_3274_);
lean_dec(v_cache_3266_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3294_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; lean_object* v___x_3285_; 
lean_inc(v_a_3260_);
v___x_3283_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_inferType_3274_, v_a_3251_, v_a_3260_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v___x_3283_);
v___x_3285_ = v___x_3281_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v_funInfo_3275_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_synthInstance_3276_);
lean_ctor_set(v_reuseFailAlloc_3293_, 3, v_whnf_3277_);
lean_ctor_set(v_reuseFailAlloc_3293_, 4, v_defEqTrans_3278_);
lean_ctor_set(v_reuseFailAlloc_3293_, 5, v_defEqPerm_3279_);
v___x_3285_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3287_; 
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 1, v___x_3285_);
v___x_3287_ = v___x_3272_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_mctx_3267_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3292_, 2, v_zetaDeltaFVarIds_3268_);
lean_ctor_set(v_reuseFailAlloc_3292_, 3, v_postponed_3269_);
lean_ctor_set(v_reuseFailAlloc_3292_, 4, v_diag_3270_);
v___x_3287_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3288_ = lean_st_ref_set(v_a_2945_, v___x_3287_);
lean_dec(v_a_2945_);
if (v_isShared_3264_ == 0)
{
v___x_3290_ = v___x_3263_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3260_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3260_);
lean_dec(v_a_3251_);
lean_dec(v_a_2945_);
return v___x_3259_;
}
}
else
{
lean_dec(v_a_3251_);
lean_dec(v_a_2945_);
return v___x_3259_;
}
}
else
{
lean_object* v_val_3298_; lean_object* v___x_3300_; 
lean_dec(v_a_3251_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec_ref(v_e_2943_);
v_val_3298_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_val_3298_);
lean_dec_ref(v___x_3258_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v_val_3298_);
v___x_3300_ = v___x_3253_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_val_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec_ref(v_e_2943_);
v_a_3303_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3250_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3250_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v___x_3311_; 
v___x_3311_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(v_e_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer___boxed(lean_object* v_e_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(lean_object* v_00_u03b2_3319_, lean_object* v_x_3320_, lean_object* v_x_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___redArg(v_x_3320_, v_x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0___boxed(lean_object* v_00_u03b2_3323_, lean_object* v_x_3324_, lean_object* v_x_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0(v_00_u03b2_3323_, v_x_3324_, v_x_3325_);
lean_dec_ref(v_x_3325_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1(lean_object* v_00_u03b2_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1___redArg(v_x_3328_, v_x_3329_, v_x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(lean_object* v_00_u03b2_3332_, lean_object* v_x_3333_, size_t v_x_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___redArg(v_x_3333_, v_x_3334_, v_x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_){
_start:
{
size_t v_x_3210__boxed_3341_; lean_object* v_res_3342_; 
v_x_3210__boxed_3341_ = lean_unbox_usize(v_x_3339_);
lean_dec(v_x_3339_);
v_res_3342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0(v_00_u03b2_3337_, v_x_3338_, v_x_3210__boxed_3341_, v_x_3340_);
lean_dec_ref(v_x_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(lean_object* v_00_u03b2_3343_, lean_object* v_x_3344_, size_t v_x_3345_, size_t v_x_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___redArg(v_x_3344_, v_x_3345_, v_x_3346_, v_x_3347_, v_x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_, lean_object* v_x_3355_){
_start:
{
size_t v_x_3221__boxed_3356_; size_t v_x_3222__boxed_3357_; lean_object* v_res_3358_; 
v_x_3221__boxed_3356_ = lean_unbox_usize(v_x_3352_);
lean_dec(v_x_3352_);
v_x_3222__boxed_3357_ = lean_unbox_usize(v_x_3353_);
lean_dec(v_x_3353_);
v_res_3358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2(v_00_u03b2_3350_, v_x_3351_, v_x_3221__boxed_3356_, v_x_3222__boxed_3357_, v_x_3354_, v_x_3355_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3359_, lean_object* v_keys_3360_, lean_object* v_vals_3361_, lean_object* v_heq_3362_, lean_object* v_i_3363_, lean_object* v_k_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___redArg(v_keys_3360_, v_vals_3361_, v_i_3363_, v_k_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3366_, lean_object* v_keys_3367_, lean_object* v_vals_3368_, lean_object* v_heq_3369_, lean_object* v_i_3370_, lean_object* v_k_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__0_spec__0_spec__1(v_00_u03b2_3366_, v_keys_3367_, v_vals_3368_, v_heq_3369_, v_i_3370_, v_k_3371_);
lean_dec_ref(v_k_3371_);
lean_dec_ref(v_vals_3368_);
lean_dec_ref(v_keys_3367_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3373_, lean_object* v_n_3374_, lean_object* v_k_3375_, lean_object* v_v_3376_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4___redArg(v_n_3374_, v_k_3375_, v_v_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_3378_, size_t v_depth_3379_, lean_object* v_keys_3380_, lean_object* v_vals_3381_, lean_object* v_heq_3382_, lean_object* v_i_3383_, lean_object* v_entries_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___redArg(v_depth_3379_, v_keys_3380_, v_vals_3381_, v_i_3383_, v_entries_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3386_, lean_object* v_depth_3387_, lean_object* v_keys_3388_, lean_object* v_vals_3389_, lean_object* v_heq_3390_, lean_object* v_i_3391_, lean_object* v_entries_3392_){
_start:
{
size_t v_depth_boxed_3393_; lean_object* v_res_3394_; 
v_depth_boxed_3393_ = lean_unbox_usize(v_depth_3387_);
lean_dec(v_depth_3387_);
v_res_3394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__5(v_00_u03b2_3386_, v_depth_boxed_3393_, v_keys_3388_, v_vals_3389_, v_heq_3390_, v_i_3391_, v_entries_3392_);
lean_dec_ref(v_vals_3389_);
lean_dec_ref(v_keys_3388_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_3395_, lean_object* v_x_3396_, lean_object* v_x_3397_, lean_object* v_x_3398_, lean_object* v_x_3399_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer_spec__1_spec__2_spec__4_spec__5___redArg(v_x_3396_, v_x_3397_, v_x_3398_, v_x_3399_);
return v___x_3400_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = l_Lean_maxRecDepthErrorMessage;
v___x_3407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
v___x_3409_ = l_Lean_MessageData_ofFormat(v___x_3408_);
return v___x_3409_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
v___x_3411_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__2));
v___x_3412_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v___x_3410_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* v_ref_3413_){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v_ref_3413_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg___boxed(lean_object* v_ref_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3418_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(lean_object* v_00_u03b1_3421_, lean_object* v_ref_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3422_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* v_00_u03b1_3429_, lean_object* v_ref_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0(v_00_u03b1_3429_, v_ref_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* v_e_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_fileName_3443_; lean_object* v_fileMap_3444_; lean_object* v_options_3445_; lean_object* v_currRecDepth_3446_; lean_object* v_maxRecDepth_3447_; lean_object* v_ref_3448_; lean_object* v_currNamespace_3449_; lean_object* v_openDecls_3450_; lean_object* v_initHeartbeats_3451_; lean_object* v_maxHeartbeats_3452_; lean_object* v_quotContext_3453_; lean_object* v_currMacroScope_3454_; uint8_t v_diag_3455_; lean_object* v_cancelTk_x3f_3456_; uint8_t v_suppressElabErrors_3457_; lean_object* v_inheritedTraceOptions_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3592_; 
v_fileName_3443_ = lean_ctor_get(v_a_3440_, 0);
v_fileMap_3444_ = lean_ctor_get(v_a_3440_, 1);
v_options_3445_ = lean_ctor_get(v_a_3440_, 2);
v_currRecDepth_3446_ = lean_ctor_get(v_a_3440_, 3);
v_maxRecDepth_3447_ = lean_ctor_get(v_a_3440_, 4);
v_ref_3448_ = lean_ctor_get(v_a_3440_, 5);
v_currNamespace_3449_ = lean_ctor_get(v_a_3440_, 6);
v_openDecls_3450_ = lean_ctor_get(v_a_3440_, 7);
v_initHeartbeats_3451_ = lean_ctor_get(v_a_3440_, 8);
v_maxHeartbeats_3452_ = lean_ctor_get(v_a_3440_, 9);
v_quotContext_3453_ = lean_ctor_get(v_a_3440_, 10);
v_currMacroScope_3454_ = lean_ctor_get(v_a_3440_, 11);
v_diag_3455_ = lean_ctor_get_uint8(v_a_3440_, sizeof(void*)*14);
v_cancelTk_x3f_3456_ = lean_ctor_get(v_a_3440_, 12);
v_suppressElabErrors_3457_ = lean_ctor_get_uint8(v_a_3440_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3458_ = lean_ctor_get(v_a_3440_, 13);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3460_ = v_a_3440_;
v_isShared_3461_ = v_isSharedCheck_3592_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_inheritedTraceOptions_3458_);
lean_inc(v_cancelTk_x3f_3456_);
lean_inc(v_currMacroScope_3454_);
lean_inc(v_quotContext_3453_);
lean_inc(v_maxHeartbeats_3452_);
lean_inc(v_initHeartbeats_3451_);
lean_inc(v_openDecls_3450_);
lean_inc(v_currNamespace_3449_);
lean_inc(v_ref_3448_);
lean_inc(v_maxRecDepth_3447_);
lean_inc(v_currRecDepth_3446_);
lean_inc(v_options_3445_);
lean_inc(v_fileMap_3444_);
lean_inc(v_fileName_3443_);
lean_dec(v_a_3440_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3592_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_nat_dec_eq(v_currRecDepth_3446_, v_maxRecDepth_3447_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; uint8_t v_transparency_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3463_ = l_Lean_Meta_Context_config(v_a_3438_);
v_transparency_3464_ = lean_ctor_get_uint8(v___x_3463_, 9);
v___x_3465_ = lean_unsigned_to_nat(1u);
v___x_3466_ = lean_nat_add(v_currRecDepth_3446_, v___x_3465_);
lean_dec(v_currRecDepth_3446_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 3, v___x_3466_);
v___x_3468_ = v___x_3460_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_fileName_3443_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_fileMap_3444_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_options_3445_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_maxRecDepth_3447_);
lean_ctor_set(v_reuseFailAlloc_3590_, 5, v_ref_3448_);
lean_ctor_set(v_reuseFailAlloc_3590_, 6, v_currNamespace_3449_);
lean_ctor_set(v_reuseFailAlloc_3590_, 7, v_openDecls_3450_);
lean_ctor_set(v_reuseFailAlloc_3590_, 8, v_initHeartbeats_3451_);
lean_ctor_set(v_reuseFailAlloc_3590_, 9, v_maxHeartbeats_3452_);
lean_ctor_set(v_reuseFailAlloc_3590_, 10, v_quotContext_3453_);
lean_ctor_set(v_reuseFailAlloc_3590_, 11, v_currMacroScope_3454_);
lean_ctor_set(v_reuseFailAlloc_3590_, 12, v_cancelTk_x3f_3456_);
lean_ctor_set(v_reuseFailAlloc_3590_, 13, v_inheritedTraceOptions_3458_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*14, v_diag_3455_);
lean_ctor_set_uint8(v_reuseFailAlloc_3590_, sizeof(void*)*14 + 1, v_suppressElabErrors_3457_);
v___x_3468_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; uint8_t v___y_3478_; uint8_t v___y_3479_; lean_object* v___y_3480_; uint8_t v___y_3509_; uint8_t v___x_3588_; uint8_t v___x_3589_; 
v___x_3588_ = 1;
v___x_3589_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_3464_, v___x_3588_);
if (v___x_3589_ == 0)
{
v___y_3509_ = v_transparency_3464_;
goto v___jp_3508_;
}
else
{
v___y_3509_ = v___x_3588_;
goto v___jp_3508_;
}
v___jp_3469_:
{
lean_object* v___x_3481_; uint8_t v_foApprox_3482_; uint8_t v_ctxApprox_3483_; uint8_t v_quasiPatternApprox_3484_; uint8_t v_constApprox_3485_; uint8_t v_isDefEqStuckEx_3486_; uint8_t v_unificationHints_3487_; uint8_t v_proofIrrelevance_3488_; uint8_t v_assignSyntheticOpaque_3489_; uint8_t v_offsetCnstrs_3490_; uint8_t v_transparency_3491_; uint8_t v_univApprox_3492_; uint8_t v_zetaUnused_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3507_; 
v___x_3481_ = l_Lean_Meta_Context_config(v___y_3470_);
lean_dec_ref(v___y_3470_);
v_foApprox_3482_ = lean_ctor_get_uint8(v___x_3481_, 0);
v_ctxApprox_3483_ = lean_ctor_get_uint8(v___x_3481_, 1);
v_quasiPatternApprox_3484_ = lean_ctor_get_uint8(v___x_3481_, 2);
v_constApprox_3485_ = lean_ctor_get_uint8(v___x_3481_, 3);
v_isDefEqStuckEx_3486_ = lean_ctor_get_uint8(v___x_3481_, 4);
v_unificationHints_3487_ = lean_ctor_get_uint8(v___x_3481_, 5);
v_proofIrrelevance_3488_ = lean_ctor_get_uint8(v___x_3481_, 6);
v_assignSyntheticOpaque_3489_ = lean_ctor_get_uint8(v___x_3481_, 7);
v_offsetCnstrs_3490_ = lean_ctor_get_uint8(v___x_3481_, 8);
v_transparency_3491_ = lean_ctor_get_uint8(v___x_3481_, 9);
v_univApprox_3492_ = lean_ctor_get_uint8(v___x_3481_, 11);
v_zetaUnused_3493_ = lean_ctor_get_uint8(v___x_3481_, 17);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3495_ = v___x_3481_;
v_isShared_3496_ = v_isSharedCheck_3507_;
goto v_resetjp_3494_;
}
else
{
lean_dec(v___x_3481_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3507_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
uint8_t v___x_3497_; uint8_t v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3501_; 
v___x_3497_ = 1;
v___x_3498_ = 0;
v___x_3499_ = 2;
if (v_isShared_3496_ == 0)
{
v___x_3501_ = v___x_3495_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 0, v_foApprox_3482_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 1, v_ctxApprox_3483_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 2, v_quasiPatternApprox_3484_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 3, v_constApprox_3485_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 4, v_isDefEqStuckEx_3486_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 5, v_unificationHints_3487_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 6, v_proofIrrelevance_3488_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 7, v_assignSyntheticOpaque_3489_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 8, v_offsetCnstrs_3490_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 9, v_transparency_3491_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 11, v_univApprox_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, 17, v_zetaUnused_3493_);
v___x_3501_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
uint64_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_ctor_set_uint8(v___x_3501_, 10, v___x_3498_);
lean_ctor_set_uint8(v___x_3501_, 12, v___x_3497_);
lean_ctor_set_uint8(v___x_3501_, 13, v___x_3497_);
lean_ctor_set_uint8(v___x_3501_, 14, v___x_3499_);
lean_ctor_set_uint8(v___x_3501_, 15, v___x_3497_);
lean_ctor_set_uint8(v___x_3501_, 16, v___x_3497_);
lean_ctor_set_uint8(v___x_3501_, 18, v___x_3497_);
v___x_3502_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3501_);
v___x_3503_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3503_, 0, v___x_3501_);
lean_ctor_set_uint64(v___x_3503_, sizeof(void*)*1, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
lean_ctor_set(v___x_3504_, 1, v___y_3472_);
lean_ctor_set(v___x_3504_, 2, v___y_3475_);
lean_ctor_set(v___x_3504_, 3, v___y_3471_);
lean_ctor_set(v___x_3504_, 4, v___y_3480_);
lean_ctor_set(v___x_3504_, 5, v___y_3477_);
lean_ctor_set(v___x_3504_, 6, v___y_3473_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*7, v___y_3474_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*7 + 1, v___y_3478_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*7 + 2, v___y_3479_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*7 + 3, v___y_3476_);
v___x_3505_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3437_, v___x_3504_, v_a_3439_, v___x_3468_, v_a_3441_);
return v___x_3505_;
}
}
}
v___jp_3508_:
{
uint8_t v_foApprox_3510_; uint8_t v_ctxApprox_3511_; uint8_t v_quasiPatternApprox_3512_; uint8_t v_constApprox_3513_; uint8_t v_isDefEqStuckEx_3514_; uint8_t v_unificationHints_3515_; uint8_t v_proofIrrelevance_3516_; uint8_t v_assignSyntheticOpaque_3517_; uint8_t v_offsetCnstrs_3518_; uint8_t v_etaStruct_3519_; uint8_t v_univApprox_3520_; uint8_t v_iota_3521_; uint8_t v_beta_3522_; uint8_t v_proj_3523_; uint8_t v_zeta_3524_; uint8_t v_zetaDelta_3525_; uint8_t v_zetaUnused_3526_; uint8_t v_zetaHave_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3587_; 
v_foApprox_3510_ = lean_ctor_get_uint8(v___x_3463_, 0);
v_ctxApprox_3511_ = lean_ctor_get_uint8(v___x_3463_, 1);
v_quasiPatternApprox_3512_ = lean_ctor_get_uint8(v___x_3463_, 2);
v_constApprox_3513_ = lean_ctor_get_uint8(v___x_3463_, 3);
v_isDefEqStuckEx_3514_ = lean_ctor_get_uint8(v___x_3463_, 4);
v_unificationHints_3515_ = lean_ctor_get_uint8(v___x_3463_, 5);
v_proofIrrelevance_3516_ = lean_ctor_get_uint8(v___x_3463_, 6);
v_assignSyntheticOpaque_3517_ = lean_ctor_get_uint8(v___x_3463_, 7);
v_offsetCnstrs_3518_ = lean_ctor_get_uint8(v___x_3463_, 8);
v_etaStruct_3519_ = lean_ctor_get_uint8(v___x_3463_, 10);
v_univApprox_3520_ = lean_ctor_get_uint8(v___x_3463_, 11);
v_iota_3521_ = lean_ctor_get_uint8(v___x_3463_, 12);
v_beta_3522_ = lean_ctor_get_uint8(v___x_3463_, 13);
v_proj_3523_ = lean_ctor_get_uint8(v___x_3463_, 14);
v_zeta_3524_ = lean_ctor_get_uint8(v___x_3463_, 15);
v_zetaDelta_3525_ = lean_ctor_get_uint8(v___x_3463_, 16);
v_zetaUnused_3526_ = lean_ctor_get_uint8(v___x_3463_, 17);
v_zetaHave_3527_ = lean_ctor_get_uint8(v___x_3463_, 18);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3529_ = v___x_3463_;
v_isShared_3530_ = v_isSharedCheck_3587_;
goto v_resetjp_3528_;
}
else
{
lean_dec(v___x_3463_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3587_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
uint8_t v_trackZetaDelta_3531_; lean_object* v_zetaDeltaSet_3532_; lean_object* v_lctx_3533_; lean_object* v_localInstances_3534_; lean_object* v_defEqCtx_x3f_3535_; lean_object* v_synthPendingDepth_3536_; lean_object* v_canUnfold_x3f_3537_; uint8_t v_univApprox_3538_; uint8_t v_inTypeClassResolution_3539_; uint8_t v_cacheInferType_3540_; lean_object* v_config_3542_; 
v_trackZetaDelta_3531_ = lean_ctor_get_uint8(v_a_3438_, sizeof(void*)*7);
v_zetaDeltaSet_3532_ = lean_ctor_get(v_a_3438_, 1);
lean_inc(v_zetaDeltaSet_3532_);
v_lctx_3533_ = lean_ctor_get(v_a_3438_, 2);
lean_inc_ref(v_lctx_3533_);
v_localInstances_3534_ = lean_ctor_get(v_a_3438_, 3);
lean_inc_ref(v_localInstances_3534_);
v_defEqCtx_x3f_3535_ = lean_ctor_get(v_a_3438_, 4);
lean_inc(v_defEqCtx_x3f_3535_);
v_synthPendingDepth_3536_ = lean_ctor_get(v_a_3438_, 5);
lean_inc(v_synthPendingDepth_3536_);
v_canUnfold_x3f_3537_ = lean_ctor_get(v_a_3438_, 6);
lean_inc(v_canUnfold_x3f_3537_);
v_univApprox_3538_ = lean_ctor_get_uint8(v_a_3438_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3539_ = lean_ctor_get_uint8(v_a_3438_, sizeof(void*)*7 + 2);
v_cacheInferType_3540_ = lean_ctor_get_uint8(v_a_3438_, sizeof(void*)*7 + 3);
if (v_isShared_3530_ == 0)
{
v_config_3542_ = v___x_3529_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 0, v_foApprox_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 1, v_ctxApprox_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 2, v_quasiPatternApprox_3512_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 3, v_constApprox_3513_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 4, v_isDefEqStuckEx_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 5, v_unificationHints_3515_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 6, v_proofIrrelevance_3516_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 7, v_assignSyntheticOpaque_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 8, v_offsetCnstrs_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 10, v_etaStruct_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 11, v_univApprox_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 12, v_iota_3521_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 13, v_beta_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 14, v_proj_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 15, v_zeta_3524_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 16, v_zetaDelta_3525_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 17, v_zetaUnused_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, 18, v_zetaHave_3527_);
v_config_3542_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
uint64_t v___x_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3578_; 
lean_ctor_set_uint8(v_config_3542_, 9, v___y_3509_);
v___x_3543_ = l_Lean_Meta_Context_configKey(v_a_3438_);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_a_3438_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; lean_object* v_unused_3582_; lean_object* v_unused_3583_; lean_object* v_unused_3584_; lean_object* v_unused_3585_; 
v_unused_3579_ = lean_ctor_get(v_a_3438_, 6);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_a_3438_, 5);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_a_3438_, 4);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_a_3438_, 3);
lean_dec(v_unused_3582_);
v_unused_3583_ = lean_ctor_get(v_a_3438_, 2);
lean_dec(v_unused_3583_);
v_unused_3584_ = lean_ctor_get(v_a_3438_, 1);
lean_dec(v_unused_3584_);
v_unused_3585_ = lean_ctor_get(v_a_3438_, 0);
lean_dec(v_unused_3585_);
v___x_3545_ = v_a_3438_;
v_isShared_3546_ = v_isSharedCheck_3578_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v_a_3438_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3578_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
uint64_t v___x_3547_; uint64_t v___x_3548_; uint64_t v___x_3549_; uint64_t v___x_3550_; uint64_t v_key_3551_; lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3547_ = 2ULL;
v___x_3548_ = lean_uint64_shift_right(v___x_3543_, v___x_3547_);
v___x_3549_ = lean_uint64_shift_left(v___x_3548_, v___x_3547_);
v___x_3550_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_3509_);
v_key_3551_ = lean_uint64_lor(v___x_3549_, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3552_, 0, v_config_3542_);
lean_ctor_set_uint64(v___x_3552_, sizeof(void*)*1, v_key_3551_);
lean_inc(v_canUnfold_x3f_3537_);
lean_inc(v_synthPendingDepth_3536_);
lean_inc(v_defEqCtx_x3f_3535_);
lean_inc_ref(v_localInstances_3534_);
lean_inc_ref(v_lctx_3533_);
lean_inc(v_zetaDeltaSet_3532_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3552_);
v___x_3554_ = v___x_3545_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3552_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_zetaDeltaSet_3532_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_lctx_3533_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_localInstances_3534_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_defEqCtx_x3f_3535_);
lean_ctor_set(v_reuseFailAlloc_3577_, 5, v_synthPendingDepth_3536_);
lean_ctor_set(v_reuseFailAlloc_3577_, 6, v_canUnfold_x3f_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*7, v_trackZetaDelta_3531_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*7 + 1, v_univApprox_3538_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3577_, sizeof(void*)*7 + 3, v_cacheInferType_3540_);
v___x_3554_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_Meta_getConfig___redArg(v___x_3554_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; uint8_t v_beta_3557_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v_beta_3557_ = lean_ctor_get_uint8(v_a_3556_, 13);
if (v_beta_3557_ == 0)
{
lean_dec(v_a_3556_);
v___y_3470_ = v___x_3554_;
v___y_3471_ = v_localInstances_3534_;
v___y_3472_ = v_zetaDeltaSet_3532_;
v___y_3473_ = v_canUnfold_x3f_3537_;
v___y_3474_ = v_trackZetaDelta_3531_;
v___y_3475_ = v_lctx_3533_;
v___y_3476_ = v_cacheInferType_3540_;
v___y_3477_ = v_synthPendingDepth_3536_;
v___y_3478_ = v_univApprox_3538_;
v___y_3479_ = v_inTypeClassResolution_3539_;
v___y_3480_ = v_defEqCtx_x3f_3535_;
goto v___jp_3469_;
}
else
{
uint8_t v_iota_3558_; 
v_iota_3558_ = lean_ctor_get_uint8(v_a_3556_, 12);
if (v_iota_3558_ == 0)
{
lean_dec(v_a_3556_);
v___y_3470_ = v___x_3554_;
v___y_3471_ = v_localInstances_3534_;
v___y_3472_ = v_zetaDeltaSet_3532_;
v___y_3473_ = v_canUnfold_x3f_3537_;
v___y_3474_ = v_trackZetaDelta_3531_;
v___y_3475_ = v_lctx_3533_;
v___y_3476_ = v_cacheInferType_3540_;
v___y_3477_ = v_synthPendingDepth_3536_;
v___y_3478_ = v_univApprox_3538_;
v___y_3479_ = v_inTypeClassResolution_3539_;
v___y_3480_ = v_defEqCtx_x3f_3535_;
goto v___jp_3469_;
}
else
{
uint8_t v_zeta_3559_; 
v_zeta_3559_ = lean_ctor_get_uint8(v_a_3556_, 15);
if (v_zeta_3559_ == 0)
{
lean_dec(v_a_3556_);
v___y_3470_ = v___x_3554_;
v___y_3471_ = v_localInstances_3534_;
v___y_3472_ = v_zetaDeltaSet_3532_;
v___y_3473_ = v_canUnfold_x3f_3537_;
v___y_3474_ = v_trackZetaDelta_3531_;
v___y_3475_ = v_lctx_3533_;
v___y_3476_ = v_cacheInferType_3540_;
v___y_3477_ = v_synthPendingDepth_3536_;
v___y_3478_ = v_univApprox_3538_;
v___y_3479_ = v_inTypeClassResolution_3539_;
v___y_3480_ = v_defEqCtx_x3f_3535_;
goto v___jp_3469_;
}
else
{
uint8_t v_zetaHave_3560_; 
v_zetaHave_3560_ = lean_ctor_get_uint8(v_a_3556_, 18);
if (v_zetaHave_3560_ == 0)
{
lean_dec(v_a_3556_);
v___y_3470_ = v___x_3554_;
v___y_3471_ = v_localInstances_3534_;
v___y_3472_ = v_zetaDeltaSet_3532_;
v___y_3473_ = v_canUnfold_x3f_3537_;
v___y_3474_ = v_trackZetaDelta_3531_;
v___y_3475_ = v_lctx_3533_;
v___y_3476_ = v_cacheInferType_3540_;
v___y_3477_ = v_synthPendingDepth_3536_;
v___y_3478_ = v_univApprox_3538_;
v___y_3479_ = v_inTypeClassResolution_3539_;
v___y_3480_ = v_defEqCtx_x3f_3535_;
goto v___jp_3469_;
}
else
{
uint8_t v_zetaDelta_3561_; 
v_zetaDelta_3561_ = lean_ctor_get_uint8(v_a_3556_, 16);
if (v_zetaDelta_3561_ == 0)
{
lean_dec(v_a_3556_);
v___y_3470_ = v___x_3554_;
v___y_3471_ = v_localInstances_3534_;
v___y_3472_ = v_zetaDeltaSet_3532_;
v___y_3473_ = v_canUnfold_x3f_3537_;
v___y_3474_ = v_trackZetaDelta_3531_;
v___y_3475_ = v_lctx_3533_;
v___y_3476_ = v_cacheInferType_3540_;
v___y_3477_ = v_synthPendingDepth_3536_;
v___y_3478_ = v_univApprox_3538_;
v___y_3479_ = v_inTypeClassResolution_3539_;
v___y_3480_ = v_defEqCtx_x3f_3535_;
goto v___jp_3469_;
}
else
{
uint8_t v_etaStruct_3562_; uint8_t v_proj_3563_; uint8_t v___x_3564_; uint8_t v___x_3565_; 
v_etaStruct_3562_ = lean_ctor_get_uint8(v_a_3556_, 10);
v_proj_3563_ = lean_ctor_get_uint8(v_a_3556_, 14);
lean_dec(v_a_3556_);
v___x_3564_ = 2;
v___x_3565_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_3563_, v___x_3564_);
if (v___x_3565_ == 0)
{
v___y_3470_ = v___x_3554_;
v___y_3471_ = v_localInstances_3534_;
v___y_3472_ = v_zetaDeltaSet_3532_;
v___y_3473_ = v_canUnfold_x3f_3537_;
v___y_3474_ = v_trackZetaDelta_3531_;
v___y_3475_ = v_lctx_3533_;
v___y_3476_ = v_cacheInferType_3540_;
v___y_3477_ = v_synthPendingDepth_3536_;
v___y_3478_ = v_univApprox_3538_;
v___y_3479_ = v_inTypeClassResolution_3539_;
v___y_3480_ = v_defEqCtx_x3f_3535_;
goto v___jp_3469_;
}
else
{
uint8_t v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = 0;
v___x_3567_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_3562_, v___x_3566_);
if (v___x_3567_ == 0)
{
v___y_3470_ = v___x_3554_;
v___y_3471_ = v_localInstances_3534_;
v___y_3472_ = v_zetaDeltaSet_3532_;
v___y_3473_ = v_canUnfold_x3f_3537_;
v___y_3474_ = v_trackZetaDelta_3531_;
v___y_3475_ = v_lctx_3533_;
v___y_3476_ = v_cacheInferType_3540_;
v___y_3477_ = v_synthPendingDepth_3536_;
v___y_3478_ = v_univApprox_3538_;
v___y_3479_ = v_inTypeClassResolution_3539_;
v___y_3480_ = v_defEqCtx_x3f_3535_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3568_; 
lean_dec(v_canUnfold_x3f_3537_);
lean_dec(v_synthPendingDepth_3536_);
lean_dec(v_defEqCtx_x3f_3535_);
lean_dec_ref(v_localInstances_3534_);
lean_dec_ref(v_lctx_3533_);
lean_dec(v_zetaDeltaSet_3532_);
v___x_3568_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferTypeImp_infer(v_e_3437_, v___x_3554_, v_a_3439_, v___x_3468_, v_a_3441_);
return v___x_3568_;
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
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v___x_3554_);
lean_dec(v_canUnfold_x3f_3537_);
lean_dec(v_synthPendingDepth_3536_);
lean_dec(v_defEqCtx_x3f_3535_);
lean_dec_ref(v_localInstances_3534_);
lean_dec_ref(v_lctx_3533_);
lean_dec(v_zetaDeltaSet_3532_);
lean_dec_ref(v___x_3468_);
lean_dec(v_a_3441_);
lean_dec(v_a_3439_);
lean_dec_ref(v_e_3437_);
v_a_3569_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3555_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3555_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
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
else
{
lean_object* v___x_3591_; 
lean_del_object(v___x_3460_);
lean_dec_ref(v_inheritedTraceOptions_3458_);
lean_dec(v_cancelTk_x3f_3456_);
lean_dec(v_currMacroScope_3454_);
lean_dec(v_quotContext_3453_);
lean_dec(v_maxHeartbeats_3452_);
lean_dec(v_initHeartbeats_3451_);
lean_dec(v_openDecls_3450_);
lean_dec(v_currNamespace_3449_);
lean_dec(v_maxRecDepth_3447_);
lean_dec(v_currRecDepth_3446_);
lean_dec_ref(v_options_3445_);
lean_dec_ref(v_fileMap_3444_);
lean_dec_ref(v_fileName_3443_);
lean_dec(v_a_3441_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec_ref(v_e_3437_);
v___x_3591_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_inferTypeImp_spec__0___redArg(v_ref_3448_);
return v___x_3591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp___boxed(lean_object* v_e_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = lean_infer_type(v_e_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v_res_3599_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* v_x_3600_){
_start:
{
switch(lean_obj_tag(v_x_3600_))
{
case 0:
{
uint8_t v___x_3601_; 
v___x_3601_ = 1;
return v___x_3601_;
}
case 2:
{
lean_object* v_a_3602_; lean_object* v_a_3603_; uint8_t v___x_3604_; 
v_a_3602_ = lean_ctor_get(v_x_3600_, 0);
v_a_3603_ = lean_ctor_get(v_x_3600_, 1);
v___x_3604_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3602_);
if (v___x_3604_ == 0)
{
return v___x_3604_;
}
else
{
v_x_3600_ = v_a_3603_;
goto _start;
}
}
case 3:
{
lean_object* v_a_3606_; 
v_a_3606_ = lean_ctor_get(v_x_3600_, 1);
v_x_3600_ = v_a_3606_;
goto _start;
}
default: 
{
uint8_t v___x_3608_; 
v___x_3608_ = 0;
return v___x_3608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* v_x_3609_){
_start:
{
uint8_t v_res_3610_; lean_object* v_r_3611_; 
v_res_3610_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_x_3609_);
lean_dec(v_x_3609_);
v_r_3611_ = lean_box(v_res_3610_);
return v_r_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* v_l_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; lean_object* v_mctx_3616_; lean_object* v___x_3617_; lean_object* v_fst_3618_; lean_object* v_snd_3619_; lean_object* v___x_3620_; lean_object* v_cache_3621_; lean_object* v_zetaDeltaFVarIds_3622_; lean_object* v_postponed_3623_; lean_object* v_diag_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3633_; 
v___x_3615_ = lean_st_ref_get(v___y_3613_);
v_mctx_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc_ref(v_mctx_3616_);
lean_dec(v___x_3615_);
v___x_3617_ = lean_instantiate_level_mvars(v_mctx_3616_, v_l_3612_);
v_fst_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_fst_3618_);
v_snd_3619_ = lean_ctor_get(v___x_3617_, 1);
lean_inc(v_snd_3619_);
lean_dec_ref(v___x_3617_);
v___x_3620_ = lean_st_ref_take(v___y_3613_);
v_cache_3621_ = lean_ctor_get(v___x_3620_, 1);
v_zetaDeltaFVarIds_3622_ = lean_ctor_get(v___x_3620_, 2);
v_postponed_3623_ = lean_ctor_get(v___x_3620_, 3);
v_diag_3624_ = lean_ctor_get(v___x_3620_, 4);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v___x_3620_, 0);
lean_dec(v_unused_3634_);
v___x_3626_ = v___x_3620_;
v_isShared_3627_ = v_isSharedCheck_3633_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_diag_3624_);
lean_inc(v_postponed_3623_);
lean_inc(v_zetaDeltaFVarIds_3622_);
lean_inc(v_cache_3621_);
lean_dec(v___x_3620_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3633_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v_fst_3618_);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_fst_3618_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_cache_3621_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_zetaDeltaFVarIds_3622_);
lean_ctor_set(v_reuseFailAlloc_3632_, 3, v_postponed_3623_);
lean_ctor_set(v_reuseFailAlloc_3632_, 4, v_diag_3624_);
v___x_3629_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_st_ref_set(v___y_3613_, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v_snd_3619_);
return v___x_3631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* v_l_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3635_, v___y_3636_);
lean_dec(v___y_3636_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* v_l_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_l_3639_, v___y_3641_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* v_l_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(v_l_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* v_x_3653_, lean_object* v_x_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
switch(lean_obj_tag(v_x_3653_))
{
case 3:
{
lean_object* v_u_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v_u_3664_ = lean_ctor_get(v_x_3653_, 0);
lean_inc(v_u_3664_);
lean_dec_ref(v_x_3653_);
v___x_3665_ = lean_unsigned_to_nat(0u);
v___x_3666_ = lean_nat_dec_eq(v_x_3654_, v___x_3665_);
lean_dec(v_x_3654_);
if (v___x_3666_ == 0)
{
lean_dec(v_u_3664_);
goto v___jp_3660_;
}
else
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3664_, v_a_3656_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3678_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3678_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
uint8_t v___x_3672_; uint8_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3672_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3668_);
lean_dec(v_a_3668_);
v___x_3673_ = l_Bool_toLBool(v___x_3672_);
v___x_3674_ = lean_box(v___x_3673_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3674_);
v___x_3676_ = v___x_3670_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
v_a_3679_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3667_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3667_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
case 7:
{
lean_object* v_body_3687_; lean_object* v_zero_3688_; uint8_t v_isZero_3689_; 
v_body_3687_ = lean_ctor_get(v_x_3653_, 2);
lean_inc_ref(v_body_3687_);
lean_dec_ref(v_x_3653_);
v_zero_3688_ = lean_unsigned_to_nat(0u);
v_isZero_3689_ = lean_nat_dec_eq(v_x_3654_, v_zero_3688_);
if (v_isZero_3689_ == 1)
{
uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
lean_dec_ref(v_body_3687_);
lean_dec(v_x_3654_);
v___x_3690_ = 0;
v___x_3691_ = lean_box(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
return v___x_3692_;
}
else
{
lean_object* v_one_3693_; lean_object* v_n_3694_; 
v_one_3693_ = lean_unsigned_to_nat(1u);
v_n_3694_ = lean_nat_sub(v_x_3654_, v_one_3693_);
lean_dec(v_x_3654_);
v_x_3653_ = v_body_3687_;
v_x_3654_ = v_n_3694_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3696_; 
v_body_3696_ = lean_ctor_get(v_x_3653_, 3);
lean_inc_ref(v_body_3696_);
lean_dec_ref(v_x_3653_);
v_x_3653_ = v_body_3696_;
goto _start;
}
case 10:
{
lean_object* v_expr_3698_; 
v_expr_3698_ = lean_ctor_get(v_x_3653_, 1);
lean_inc_ref(v_expr_3698_);
lean_dec_ref(v_x_3653_);
v_x_3653_ = v_expr_3698_;
goto _start;
}
default: 
{
lean_dec(v_x_3654_);
lean_dec_ref(v_x_3653_);
goto v___jp_3660_;
}
}
v___jp_3660_:
{
uint8_t v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = 2;
v___x_3662_ = lean_box(v___x_3661_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_x_3700_, v_x_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
lean_dec(v_a_3705_);
lean_dec_ref(v_a_3704_);
lean_dec(v_a_3703_);
lean_dec_ref(v_a_3702_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* v_x_3708_, lean_object* v_x_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
switch(lean_obj_tag(v_x_3708_))
{
case 4:
{
lean_object* v_declName_3715_; lean_object* v_us_3716_; lean_object* v___x_3717_; 
v_declName_3715_ = lean_ctor_get(v_x_3708_, 0);
lean_inc(v_declName_3715_);
v_us_3716_ = lean_ctor_get(v_x_3708_, 1);
lean_inc(v_us_3716_);
lean_dec_ref(v_x_3708_);
lean_inc_ref(v_a_3712_);
v___x_3717_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3715_, v_us_3716_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3718_, v_x_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
return v___x_3719_;
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
lean_dec(v_x_3709_);
v_a_3720_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3717_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3717_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3728_; lean_object* v___x_3729_; 
v_fvarId_3728_ = lean_ctor_get(v_x_3708_, 0);
lean_inc(v_fvarId_3728_);
lean_dec_ref(v_x_3708_);
lean_inc_ref(v_a_3710_);
v___x_3729_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3728_, v_a_3710_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref(v___x_3729_);
v___x_3731_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3730_, v_x_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
return v___x_3731_;
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
lean_dec(v_x_3709_);
v_a_3732_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3729_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3729_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3740_; lean_object* v___x_3741_; 
v_mvarId_3740_ = lean_ctor_get(v_x_3708_, 0);
lean_inc(v_mvarId_3740_);
lean_dec_ref(v_x_3708_);
v___x_3741_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3740_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3743_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3742_);
lean_dec_ref(v___x_3741_);
v___x_3743_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3742_, v_x_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
return v___x_3743_;
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
lean_dec(v_x_3709_);
v_a_3744_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3741_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3741_);
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
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
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
}
case 5:
{
lean_object* v_fn_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_fn_3752_ = lean_ctor_get(v_x_3708_, 0);
lean_inc_ref(v_fn_3752_);
lean_dec_ref(v_x_3708_);
v___x_3753_ = lean_unsigned_to_nat(1u);
v___x_3754_ = lean_nat_add(v_x_3709_, v___x_3753_);
lean_dec(v_x_3709_);
v_x_3708_ = v_fn_3752_;
v_x_3709_ = v___x_3754_;
goto _start;
}
case 10:
{
lean_object* v_expr_3756_; 
v_expr_3756_ = lean_ctor_get(v_x_3708_, 1);
lean_inc_ref(v_expr_3756_);
lean_dec_ref(v_x_3708_);
v_x_3708_ = v_expr_3756_;
goto _start;
}
case 8:
{
lean_object* v_body_3758_; 
v_body_3758_ = lean_ctor_get(v_x_3708_, 3);
lean_inc_ref(v_body_3758_);
lean_dec_ref(v_x_3708_);
v_x_3708_ = v_body_3758_;
goto _start;
}
case 6:
{
lean_object* v_body_3760_; lean_object* v_zero_3761_; uint8_t v_isZero_3762_; 
v_body_3760_ = lean_ctor_get(v_x_3708_, 2);
lean_inc_ref(v_body_3760_);
lean_dec_ref(v_x_3708_);
v_zero_3761_ = lean_unsigned_to_nat(0u);
v_isZero_3762_ = lean_nat_dec_eq(v_x_3709_, v_zero_3761_);
if (v_isZero_3762_ == 1)
{
uint8_t v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
lean_dec_ref(v_body_3760_);
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
lean_dec(v_x_3709_);
v___x_3763_ = 0;
v___x_3764_ = lean_box(v___x_3763_);
v___x_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
return v___x_3765_;
}
else
{
lean_object* v_one_3766_; lean_object* v_n_3767_; 
v_one_3766_ = lean_unsigned_to_nat(1u);
v_n_3767_ = lean_nat_sub(v_x_3709_, v_one_3766_);
lean_dec(v_x_3709_);
v_x_3708_ = v_body_3760_;
v_x_3709_ = v_n_3767_;
goto _start;
}
}
default: 
{
uint8_t v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
lean_dec_ref(v_a_3712_);
lean_dec_ref(v_a_3710_);
lean_dec(v_x_3709_);
lean_dec_ref(v_x_3708_);
v___x_3769_ = 2;
v___x_3770_ = lean_box(v___x_3769_);
v___x_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
return v___x_3771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* v_x_3772_, lean_object* v_x_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_x_3772_, v_x_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec(v_a_3777_);
lean_dec(v_a_3775_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* v_x_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_){
_start:
{
switch(lean_obj_tag(v_x_3780_))
{
case 0:
{
uint8_t v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_dec_ref(v_x_3780_);
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
v___x_3786_ = 2;
v___x_3787_ = lean_box(v___x_3786_);
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
return v___x_3788_;
}
case 1:
{
lean_object* v_fvarId_3789_; lean_object* v___x_3790_; 
v_fvarId_3789_ = lean_ctor_get(v_x_3780_, 0);
lean_inc(v_fvarId_3789_);
lean_dec_ref(v_x_3780_);
lean_inc_ref(v_a_3781_);
v___x_3790_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_3789_, v_a_3781_, v_a_3783_, v_a_3784_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref(v___x_3790_);
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3791_, v___x_3792_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
return v___x_3793_;
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
v_a_3794_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3790_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3790_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_3802_; lean_object* v___x_3803_; 
v_mvarId_3802_ = lean_ctor_get(v_x_3780_, 0);
lean_inc(v_mvarId_3802_);
lean_dec_ref(v_x_3780_);
v___x_3803_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_3802_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = lean_unsigned_to_nat(0u);
v___x_3806_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3804_, v___x_3805_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
return v___x_3806_;
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
v_a_3807_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3803_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3803_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
case 4:
{
lean_object* v_declName_3815_; lean_object* v_us_3816_; lean_object* v___x_3817_; 
v_declName_3815_ = lean_ctor_get(v_x_3780_, 0);
lean_inc(v_declName_3815_);
v_us_3816_ = lean_ctor_get(v_x_3780_, 1);
lean_inc(v_us_3816_);
lean_dec_ref(v_x_3780_);
lean_inc_ref(v_a_3783_);
v___x_3817_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_3815_, v_us_3816_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3817_);
v___x_3819_ = lean_unsigned_to_nat(0u);
v___x_3820_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(v_a_3818_, v___x_3819_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
return v___x_3820_;
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
v_a_3821_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3817_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3817_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
case 5:
{
lean_object* v_fn_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_fn_3829_ = lean_ctor_get(v_x_3780_, 0);
lean_inc_ref(v_fn_3829_);
lean_dec_ref(v_x_3780_);
v___x_3830_ = lean_unsigned_to_nat(1u);
v___x_3831_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(v_fn_3829_, v___x_3830_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
return v___x_3831_;
}
case 7:
{
lean_object* v_body_3832_; 
v_body_3832_ = lean_ctor_get(v_x_3780_, 2);
lean_inc_ref(v_body_3832_);
lean_dec_ref(v_x_3780_);
v_x_3780_ = v_body_3832_;
goto _start;
}
case 8:
{
lean_object* v_body_3834_; 
v_body_3834_ = lean_ctor_get(v_x_3780_, 3);
lean_inc_ref(v_body_3834_);
lean_dec_ref(v_x_3780_);
v_x_3780_ = v_body_3834_;
goto _start;
}
case 10:
{
lean_object* v_expr_3836_; 
v_expr_3836_ = lean_ctor_get(v_x_3780_, 1);
lean_inc_ref(v_expr_3836_);
lean_dec_ref(v_x_3780_);
v_x_3780_ = v_expr_3836_;
goto _start;
}
case 11:
{
uint8_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
lean_dec_ref(v_x_3780_);
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
v___x_3838_ = 2;
v___x_3839_ = lean_box(v___x_3838_);
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
return v___x_3840_;
}
default: 
{
uint8_t v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec_ref(v_a_3783_);
lean_dec_ref(v_a_3781_);
lean_dec_ref(v_x_3780_);
v___x_3841_ = 0;
v___x_3842_ = lean_box(v___x_3841_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* v_x_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Meta_isPropQuick(v_x_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
lean_dec(v_a_3848_);
lean_dec(v_a_3846_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* v_e_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v___x_3857_; 
lean_inc_ref(v_a_3854_);
lean_inc_ref(v_a_3852_);
lean_inc_ref(v_e_3851_);
v___x_3857_ = l_Lean_Meta_isPropQuick(v_e_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3914_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3914_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3914_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
uint8_t v___x_3862_; 
v___x_3862_ = lean_unbox(v_a_3858_);
lean_dec(v_a_3858_);
switch(v___x_3862_)
{
case 0:
{
uint8_t v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; 
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec_ref(v_e_3851_);
v___x_3863_ = 0;
v___x_3864_ = lean_box(v___x_3863_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3864_);
v___x_3866_ = v___x_3860_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
case 1:
{
uint8_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec_ref(v_e_3851_);
v___x_3868_ = 1;
v___x_3869_ = lean_box(v___x_3868_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3869_);
v___x_3871_ = v___x_3860_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
default: 
{
lean_object* v___x_3873_; 
lean_del_object(v___x_3860_);
lean_inc(v_a_3855_);
lean_inc_ref(v_a_3854_);
lean_inc(v_a_3853_);
lean_inc_ref(v_a_3852_);
v___x_3873_ = lean_infer_type(v_e_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref(v___x_3873_);
lean_inc(v_a_3853_);
v___x_3875_ = l_Lean_Meta_whnfD(v_a_3874_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3897_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3878_ = v___x_3875_;
v_isShared_3879_ = v_isSharedCheck_3897_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3875_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3897_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
if (lean_obj_tag(v_a_3876_) == 3)
{
lean_object* v_u_3880_; lean_object* v___x_3881_; lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3891_; 
lean_del_object(v___x_3878_);
v_u_3880_ = lean_ctor_get(v_a_3876_, 0);
lean_inc(v_u_3880_);
lean_dec_ref(v_a_3876_);
v___x_3881_ = l_Lean_instantiateLevelMVars___at___00__private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(v_u_3880_, v_a_3853_);
lean_dec(v_a_3853_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
uint8_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3886_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(v_a_3882_);
lean_dec(v_a_3882_);
v___x_3887_ = lean_box(v___x_3886_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3887_);
v___x_3889_ = v___x_3884_;
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
uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
lean_dec(v_a_3876_);
lean_dec(v_a_3853_);
v___x_3892_ = 0;
v___x_3893_ = lean_box(v___x_3892_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v___x_3893_);
v___x_3895_ = v___x_3878_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec(v_a_3853_);
v_a_3898_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3875_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3875_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
v_a_3906_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3873_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3873_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec_ref(v_e_3851_);
v_a_3915_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3857_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3857_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp___boxed(lean_object* v_e_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_Meta_isProp(v_e_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(lean_object* v_x_3930_){
_start:
{
switch(lean_obj_tag(v_x_3930_))
{
case 0:
{
lean_object* v___x_3931_; 
v___x_3931_ = lean_unsigned_to_nat(0u);
return v___x_3931_;
}
case 1:
{
lean_object* v___x_3932_; 
v___x_3932_ = lean_unsigned_to_nat(1u);
return v___x_3932_;
}
case 2:
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_unsigned_to_nat(2u);
return v___x_3933_;
}
default: 
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_unsigned_to_nat(3u);
return v___x_3934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx___boxed(lean_object* v_x_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorIdx(v_x_3935_);
lean_dec(v_x_3935_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(lean_object* v_t_3937_, lean_object* v_k_3938_){
_start:
{
if (lean_obj_tag(v_t_3937_) == 3)
{
lean_object* v_idx_3939_; lean_object* v___x_3940_; 
v_idx_3939_ = lean_ctor_get(v_t_3937_, 0);
lean_inc(v_idx_3939_);
lean_dec_ref(v_t_3937_);
v___x_3940_ = lean_apply_1(v_k_3938_, v_idx_3939_);
return v___x_3940_;
}
else
{
lean_dec(v_t_3937_);
return v_k_3938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(lean_object* v_motive_3941_, lean_object* v_ctorIdx_3942_, lean_object* v_t_3943_, lean_object* v_h_3944_, lean_object* v_k_3945_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3943_, v_k_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___boxed(lean_object* v_motive_3947_, lean_object* v_ctorIdx_3948_, lean_object* v_t_3949_, lean_object* v_h_3950_, lean_object* v_k_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim(v_motive_3947_, v_ctorIdx_3948_, v_t_3949_, v_h_3950_, v_k_3951_);
lean_dec(v_ctorIdx_3948_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim___redArg(lean_object* v_t_3953_, lean_object* v_false_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3953_, v_false_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_false_elim(lean_object* v_motive_3956_, lean_object* v_t_3957_, lean_object* v_h_3958_, lean_object* v_false_3959_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3957_, v_false_3959_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim___redArg(lean_object* v_t_3961_, lean_object* v_true_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3961_, v_true_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_true_elim(lean_object* v_motive_3964_, lean_object* v_t_3965_, lean_object* v_h_3966_, lean_object* v_true_3967_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3965_, v_true_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim___redArg(lean_object* v_t_3969_, lean_object* v_undef_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3969_, v_undef_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_undef_elim(lean_object* v_motive_3972_, lean_object* v_t_3973_, lean_object* v_h_3974_, lean_object* v_undef_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3973_, v_undef_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim___redArg(lean_object* v_t_3977_, lean_object* v_bvar_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3977_, v_bvar_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_bvar_elim(lean_object* v_motive_3980_, lean_object* v_t_3981_, lean_object* v_h_3982_, lean_object* v_bvar_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_ctorElim___redArg(v_t_3981_, v_bvar_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t v_x_3985_){
_start:
{
switch(v_x_3985_)
{
case 0:
{
lean_object* v___x_3986_; 
v___x_3986_ = lean_box(0);
return v___x_3986_;
}
case 1:
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_box(1);
return v___x_3987_;
}
default: 
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_box(2);
return v___x_3988_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* v_x_3989_){
_start:
{
uint8_t v_x_25__boxed_3990_; lean_object* v_res_3991_; 
v_x_25__boxed_3990_ = lean_unbox(v_x_3989_);
v_res_3991_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v_x_25__boxed_3990_);
return v_res_3991_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* v_x_3992_){
_start:
{
switch(lean_obj_tag(v_x_3992_))
{
case 0:
{
uint8_t v___x_3993_; 
v___x_3993_ = 0;
return v___x_3993_;
}
case 1:
{
uint8_t v___x_3994_; 
v___x_3994_ = 1;
return v___x_3994_;
}
default: 
{
uint8_t v___x_3995_; 
v___x_3995_ = 2;
return v___x_3995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* v_x_3996_){
_start:
{
uint8_t v_res_3997_; lean_object* v_r_3998_; 
v_res_3997_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_x_3996_);
lean_dec(v_x_3996_);
v_r_3998_ = lean_box(v_res_3997_);
return v_r_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* v_e_4000_){
_start:
{
switch(lean_obj_tag(v_e_4000_))
{
case 3:
{
lean_object* v_u_4001_; uint8_t v___x_4002_; 
v_u_4001_ = lean_ctor_get(v_e_4000_, 0);
v___x_4002_ = l_Lean_Level_isNeverZero(v_u_4001_);
if (v___x_4002_ == 0)
{
uint8_t v___x_4003_; 
v___x_4003_ = l_Lean_Level_isZero(v_u_4001_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_box(2);
return v___x_4004_;
}
else
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_box(1);
return v___x_4005_;
}
}
else
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_box(0);
return v___x_4006_;
}
}
case 5:
{
lean_object* v_fn_4007_; 
v_fn_4007_ = lean_ctor_get(v_e_4000_, 0);
if (lean_obj_tag(v_fn_4007_) == 4)
{
lean_object* v_declName_4008_; 
v_declName_4008_ = lean_ctor_get(v_fn_4007_, 0);
if (lean_obj_tag(v_declName_4008_) == 1)
{
lean_object* v_pre_4009_; 
v_pre_4009_ = lean_ctor_get(v_declName_4008_, 0);
if (lean_obj_tag(v_pre_4009_) == 0)
{
lean_object* v_arg_4010_; lean_object* v_str_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v_arg_4010_ = lean_ctor_get(v_e_4000_, 1);
v_str_4011_ = lean_ctor_get(v_declName_4008_, 1);
v___x_4012_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0));
v___x_4013_ = lean_string_dec_eq(v_str_4011_, v___x_4012_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_box(2);
return v___x_4014_;
}
else
{
v_e_4000_ = v_arg_4010_;
goto _start;
}
}
else
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_box(2);
return v___x_4016_;
}
}
else
{
lean_object* v___x_4017_; 
v___x_4017_ = lean_box(2);
return v___x_4017_;
}
}
else
{
lean_object* v___x_4018_; 
v___x_4018_ = lean_box(2);
return v___x_4018_;
}
}
default: 
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_box(2);
return v___x_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* v_e_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_e_4020_);
lean_dec_ref(v_e_4020_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* v_r_4022_, lean_object* v_binderType_4023_){
_start:
{
if (lean_obj_tag(v_r_4022_) == 3)
{
lean_object* v_idx_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4036_; 
v_idx_4024_ = lean_ctor_get(v_r_4022_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_r_4022_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4026_ = v_r_4022_;
v_isShared_4027_ = v_isSharedCheck_4036_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_idx_4024_);
lean_dec(v_r_4022_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4036_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_zero_4028_; uint8_t v_isZero_4029_; 
v_zero_4028_ = lean_unsigned_to_nat(0u);
v_isZero_4029_ = lean_nat_dec_eq(v_idx_4024_, v_zero_4028_);
if (v_isZero_4029_ == 1)
{
lean_object* v___x_4030_; 
lean_del_object(v___x_4026_);
lean_dec(v_idx_4024_);
v___x_4030_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(v_binderType_4023_);
return v___x_4030_;
}
else
{
lean_object* v_one_4031_; lean_object* v_n_4032_; lean_object* v___x_4034_; 
v_one_4031_ = lean_unsigned_to_nat(1u);
v_n_4032_ = lean_nat_sub(v_idx_4024_, v_one_4031_);
lean_dec(v_idx_4024_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v_n_4032_);
v___x_4034_ = v___x_4026_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_n_4032_);
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
else
{
return v_r_4022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* v_r_4037_, lean_object* v_binderType_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_r_4037_, v_binderType_4038_);
lean_dec_ref(v_binderType_4038_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* v_x_4040_, lean_object* v_x_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_){
_start:
{
lean_object* v_type_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; 
switch(lean_obj_tag(v_x_4040_))
{
case 7:
{
lean_object* v_binderType_4075_; lean_object* v_body_4076_; lean_object* v_zero_4077_; uint8_t v_isZero_4078_; 
v_binderType_4075_ = lean_ctor_get(v_x_4040_, 1);
v_body_4076_ = lean_ctor_get(v_x_4040_, 2);
v_zero_4077_ = lean_unsigned_to_nat(0u);
v_isZero_4078_ = lean_nat_dec_eq(v_x_4041_, v_zero_4077_);
if (v_isZero_4078_ == 1)
{
v_type_4048_ = v_x_4040_;
v___y_4049_ = v_a_4042_;
v___y_4050_ = v_a_4043_;
v___y_4051_ = v_a_4044_;
v___y_4052_ = v_a_4045_;
goto v___jp_4047_;
}
else
{
lean_object* v_one_4079_; lean_object* v_n_4080_; lean_object* v___x_4081_; 
lean_inc_ref(v_body_4076_);
lean_inc_ref(v_binderType_4075_);
lean_dec_ref(v_x_4040_);
v_one_4079_ = lean_unsigned_to_nat(1u);
v_n_4080_ = lean_nat_sub(v_x_4041_, v_one_4079_);
v___x_4081_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4076_, v_n_4080_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_n_4080_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4090_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4090_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4090_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4086_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4082_, v_binderType_4075_);
lean_dec_ref(v_binderType_4075_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v___x_4086_);
v___x_4088_ = v___x_4084_;
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
lean_dec_ref(v_binderType_4075_);
return v___x_4081_;
}
}
}
case 8:
{
lean_object* v_type_4091_; lean_object* v_body_4092_; lean_object* v___x_4093_; 
v_type_4091_ = lean_ctor_get(v_x_4040_, 1);
lean_inc_ref(v_type_4091_);
v_body_4092_ = lean_ctor_get(v_x_4040_, 3);
lean_inc_ref(v_body_4092_);
lean_dec_ref(v_x_4040_);
v___x_4093_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_body_4092_, v_x_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4102_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4096_ = v___x_4093_;
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4093_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4098_; lean_object* v___x_4100_; 
v___x_4098_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(v_a_4094_, v_type_4091_);
lean_dec_ref(v_type_4091_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4098_);
v___x_4100_ = v___x_4096_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
else
{
lean_dec_ref(v_type_4091_);
return v___x_4093_;
}
}
case 10:
{
lean_object* v_expr_4103_; 
v_expr_4103_ = lean_ctor_get(v_x_4040_, 1);
lean_inc_ref(v_expr_4103_);
lean_dec_ref(v_x_4040_);
v_x_4040_ = v_expr_4103_;
goto _start;
}
case 0:
{
lean_object* v_deBruijnIndex_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
lean_dec_ref(v_a_4044_);
lean_dec_ref(v_a_4042_);
v_deBruijnIndex_4105_ = lean_ctor_get(v_x_4040_, 0);
lean_inc(v_deBruijnIndex_4105_);
lean_dec_ref(v_x_4040_);
v___x_4106_ = lean_unsigned_to_nat(0u);
v___x_4107_ = lean_nat_dec_eq(v_x_4041_, v___x_4106_);
if (v___x_4107_ == 0)
{
lean_dec(v_deBruijnIndex_4105_);
goto v___jp_4072_;
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_deBruijnIndex_4105_);
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
return v___x_4109_;
}
}
default: 
{
lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4110_ = lean_unsigned_to_nat(0u);
v___x_4111_ = lean_nat_dec_eq(v_x_4041_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_dec_ref(v_a_4044_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_x_4040_);
goto v___jp_4072_;
}
else
{
v_type_4048_ = v_x_4040_;
v___y_4049_ = v_a_4042_;
v___y_4050_ = v_a_4043_;
v___y_4051_ = v_a_4044_;
v___y_4052_ = v_a_4045_;
goto v___jp_4047_;
}
}
}
v___jp_4047_:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_Meta_isPropQuick(v_type_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4063_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4056_ = v___x_4053_;
v_isShared_4057_ = v_isSharedCheck_4063_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4053_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4063_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
uint8_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4058_ = lean_unbox(v_a_4054_);
lean_dec(v_a_4054_);
v___x_4059_ = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(v___x_4058_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v___x_4059_);
v___x_4061_ = v___x_4056_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_a_4064_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4053_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4053_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
v___jp_4072_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = lean_box(2);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* v_x_4112_, lean_object* v_x_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_x_4112_, v_x_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
lean_dec(v_a_4117_);
lean_dec(v_a_4115_);
lean_dec(v_x_4113_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* v_e_4120_, lean_object* v_n_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(v_e_4120_, v_n_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4137_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4130_ = v___x_4127_;
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4137_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
uint8_t v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4132_ = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(v_a_4128_);
lean_dec(v_a_4128_);
v___x_4133_ = lean_box(v___x_4132_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4133_);
v___x_4135_ = v___x_4130_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
v_a_4138_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4127_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4127_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* v_e_4146_, lean_object* v_n_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_e_4146_, v_n_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_);
lean_dec(v_a_4151_);
lean_dec(v_a_4149_);
lean_dec(v_n_4147_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* v_x_4154_, lean_object* v_x_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_){
_start:
{
switch(lean_obj_tag(v_x_4154_))
{
case 4:
{
lean_object* v_declName_4161_; lean_object* v_us_4162_; lean_object* v___x_4163_; 
v_declName_4161_ = lean_ctor_get(v_x_4154_, 0);
lean_inc(v_declName_4161_);
v_us_4162_ = lean_ctor_get(v_x_4154_, 1);
lean_inc(v_us_4162_);
lean_dec_ref(v_x_4154_);
lean_inc_ref(v_a_4158_);
v___x_4163_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4161_, v_us_4162_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4165_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref(v___x_4163_);
v___x_4165_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4164_, v_x_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_x_4155_);
return v___x_4165_;
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v_a_4158_);
lean_dec_ref(v_a_4156_);
lean_dec(v_x_4155_);
v_a_4166_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4163_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4163_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4174_; lean_object* v___x_4175_; 
v_fvarId_4174_ = lean_ctor_get(v_x_4154_, 0);
lean_inc(v_fvarId_4174_);
lean_dec_ref(v_x_4154_);
lean_inc_ref(v_a_4156_);
v___x_4175_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4174_, v_a_4156_, v_a_4158_, v_a_4159_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref(v___x_4175_);
v___x_4177_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4176_, v_x_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_x_4155_);
return v___x_4177_;
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_dec_ref(v_a_4158_);
lean_dec_ref(v_a_4156_);
lean_dec(v_x_4155_);
v_a_4178_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4175_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4175_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4186_; lean_object* v___x_4187_; 
v_mvarId_4186_ = lean_ctor_get(v_x_4154_, 0);
lean_inc(v_mvarId_4186_);
lean_dec_ref(v_x_4154_);
v___x_4187_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4186_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4189_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref(v___x_4187_);
v___x_4189_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4188_, v_x_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_x_4155_);
return v___x_4189_;
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec_ref(v_a_4158_);
lean_dec_ref(v_a_4156_);
lean_dec(v_x_4155_);
v_a_4190_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4187_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4187_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
case 5:
{
lean_object* v_fn_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v_fn_4198_ = lean_ctor_get(v_x_4154_, 0);
lean_inc_ref(v_fn_4198_);
lean_dec_ref(v_x_4154_);
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_nat_add(v_x_4155_, v___x_4199_);
lean_dec(v_x_4155_);
v_x_4154_ = v_fn_4198_;
v_x_4155_ = v___x_4200_;
goto _start;
}
case 10:
{
lean_object* v_expr_4202_; 
v_expr_4202_ = lean_ctor_get(v_x_4154_, 1);
lean_inc_ref(v_expr_4202_);
lean_dec_ref(v_x_4154_);
v_x_4154_ = v_expr_4202_;
goto _start;
}
case 8:
{
lean_object* v_body_4204_; 
v_body_4204_ = lean_ctor_get(v_x_4154_, 3);
lean_inc_ref(v_body_4204_);
lean_dec_ref(v_x_4154_);
v_x_4154_ = v_body_4204_;
goto _start;
}
case 6:
{
lean_object* v_body_4206_; lean_object* v_zero_4207_; uint8_t v_isZero_4208_; 
v_body_4206_ = lean_ctor_get(v_x_4154_, 2);
lean_inc_ref(v_body_4206_);
lean_dec_ref(v_x_4154_);
v_zero_4207_ = lean_unsigned_to_nat(0u);
v_isZero_4208_ = lean_nat_dec_eq(v_x_4155_, v_zero_4207_);
if (v_isZero_4208_ == 1)
{
lean_object* v___x_4209_; 
lean_dec(v_x_4155_);
v___x_4209_ = l_Lean_Meta_isProofQuick(v_body_4206_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
return v___x_4209_;
}
else
{
lean_object* v_one_4210_; lean_object* v_n_4211_; 
v_one_4210_ = lean_unsigned_to_nat(1u);
v_n_4211_ = lean_nat_sub(v_x_4155_, v_one_4210_);
lean_dec(v_x_4155_);
v_x_4154_ = v_body_4206_;
v_x_4155_ = v_n_4211_;
goto _start;
}
}
default: 
{
uint8_t v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_dec_ref(v_a_4158_);
lean_dec_ref(v_a_4156_);
lean_dec(v_x_4155_);
lean_dec_ref(v_x_4154_);
v___x_4213_ = 2;
v___x_4214_ = lean_box(v___x_4213_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* v_x_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
switch(lean_obj_tag(v_x_4216_))
{
case 0:
{
uint8_t v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_dec_ref(v_x_4216_);
lean_dec_ref(v_a_4219_);
lean_dec_ref(v_a_4217_);
v___x_4222_ = 2;
v___x_4223_ = lean_box(v___x_4222_);
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
return v___x_4224_;
}
case 1:
{
lean_object* v_fvarId_4225_; lean_object* v___x_4226_; 
v_fvarId_4225_ = lean_ctor_get(v_x_4216_, 0);
lean_inc(v_fvarId_4225_);
lean_dec_ref(v_x_4216_);
lean_inc_ref(v_a_4217_);
v___x_4226_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4225_, v_a_4217_, v_a_4219_, v_a_4220_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref(v___x_4226_);
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4227_, v___x_4228_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
return v___x_4229_;
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec_ref(v_a_4219_);
lean_dec_ref(v_a_4217_);
v_a_4230_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4226_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4226_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4238_; lean_object* v___x_4239_; 
v_mvarId_4238_ = lean_ctor_get(v_x_4216_, 0);
lean_inc(v_mvarId_4238_);
lean_dec_ref(v_x_4216_);
v___x_4239_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4238_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref(v___x_4239_);
v___x_4241_ = lean_unsigned_to_nat(0u);
v___x_4242_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4240_, v___x_4241_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
return v___x_4242_;
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v_a_4219_);
lean_dec_ref(v_a_4217_);
v_a_4243_ = lean_ctor_get(v___x_4239_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4239_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4239_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4239_);
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
case 4:
{
lean_object* v_declName_4251_; lean_object* v_us_4252_; lean_object* v___x_4253_; 
v_declName_4251_ = lean_ctor_get(v_x_4216_, 0);
lean_inc(v_declName_4251_);
v_us_4252_ = lean_ctor_get(v_x_4216_, 1);
lean_inc(v_us_4252_);
lean_dec_ref(v_x_4216_);
lean_inc_ref(v_a_4219_);
v___x_4253_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4251_, v_us_4252_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref(v___x_4253_);
v___x_4255_ = lean_unsigned_to_nat(0u);
v___x_4256_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(v_a_4254_, v___x_4255_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
return v___x_4256_;
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec_ref(v_a_4219_);
lean_dec_ref(v_a_4217_);
v_a_4257_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4253_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4253_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
case 5:
{
lean_object* v_fn_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v_fn_4265_ = lean_ctor_get(v_x_4216_, 0);
lean_inc_ref(v_fn_4265_);
lean_dec_ref(v_x_4216_);
v___x_4266_ = lean_unsigned_to_nat(1u);
v___x_4267_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_fn_4265_, v___x_4266_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
return v___x_4267_;
}
case 6:
{
lean_object* v_body_4268_; 
v_body_4268_ = lean_ctor_get(v_x_4216_, 2);
lean_inc_ref(v_body_4268_);
lean_dec_ref(v_x_4216_);
v_x_4216_ = v_body_4268_;
goto _start;
}
case 8:
{
lean_object* v_body_4270_; 
v_body_4270_ = lean_ctor_get(v_x_4216_, 3);
lean_inc_ref(v_body_4270_);
lean_dec_ref(v_x_4216_);
v_x_4216_ = v_body_4270_;
goto _start;
}
case 10:
{
lean_object* v_expr_4272_; 
v_expr_4272_ = lean_ctor_get(v_x_4216_, 1);
lean_inc_ref(v_expr_4272_);
lean_dec_ref(v_x_4216_);
v_x_4216_ = v_expr_4272_;
goto _start;
}
case 11:
{
uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
lean_dec_ref(v_x_4216_);
lean_dec_ref(v_a_4219_);
lean_dec_ref(v_a_4217_);
v___x_4274_ = 2;
v___x_4275_ = lean_box(v___x_4274_);
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
return v___x_4276_;
}
default: 
{
uint8_t v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
lean_dec_ref(v_a_4219_);
lean_dec_ref(v_a_4217_);
lean_dec_ref(v_x_4216_);
v___x_4277_ = 0;
v___x_4278_ = lean_box(v___x_4277_);
v___x_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
return v___x_4279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* v_x_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Meta_isProofQuick(v_x_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
lean_dec(v_a_4284_);
lean_dec(v_a_4282_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* v_x_4287_, lean_object* v_x_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(v_x_4287_, v_x_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_);
lean_dec(v_a_4292_);
lean_dec(v_a_4290_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* v_e_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v___x_4301_; 
lean_inc_ref(v_a_4298_);
lean_inc_ref(v_a_4296_);
lean_inc_ref(v_e_4295_);
v___x_4301_ = l_Lean_Meta_isProofQuick(v_e_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4328_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4328_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4328_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
uint8_t v___x_4306_; 
v___x_4306_ = lean_unbox(v_a_4302_);
lean_dec(v_a_4302_);
switch(v___x_4306_)
{
case 0:
{
uint8_t v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec_ref(v_e_4295_);
v___x_4307_ = 0;
v___x_4308_ = lean_box(v___x_4307_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4308_);
v___x_4310_ = v___x_4304_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
case 1:
{
uint8_t v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4315_; 
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec_ref(v_e_4295_);
v___x_4312_ = 1;
v___x_4313_ = lean_box(v___x_4312_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4313_);
v___x_4315_ = v___x_4304_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
default: 
{
lean_object* v___x_4317_; 
lean_del_object(v___x_4304_);
lean_inc(v_a_4299_);
lean_inc_ref(v_a_4298_);
lean_inc(v_a_4297_);
lean_inc_ref(v_a_4296_);
v___x_4317_ = lean_infer_type(v_e_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref(v___x_4317_);
v___x_4319_ = l_Lean_Meta_isProp(v_a_4318_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
return v___x_4319_;
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
v_a_4320_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4317_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4317_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec_ref(v_e_4295_);
v_a_4329_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4301_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4301_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof___boxed(lean_object* v_e_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_Meta_isProof(v_e_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* v_x_4344_, lean_object* v_x_4345_){
_start:
{
switch(lean_obj_tag(v_x_4344_))
{
case 3:
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = lean_nat_dec_eq(v_x_4345_, v___x_4351_);
lean_dec(v_x_4345_);
if (v___x_4352_ == 0)
{
goto v___jp_4347_;
}
else
{
uint8_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = 1;
v___x_4354_ = lean_box(v___x_4353_);
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
return v___x_4355_;
}
}
case 7:
{
lean_object* v_body_4356_; lean_object* v_zero_4357_; uint8_t v_isZero_4358_; 
v_body_4356_ = lean_ctor_get(v_x_4344_, 2);
v_zero_4357_ = lean_unsigned_to_nat(0u);
v_isZero_4358_ = lean_nat_dec_eq(v_x_4345_, v_zero_4357_);
if (v_isZero_4358_ == 1)
{
uint8_t v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
lean_dec(v_x_4345_);
v___x_4359_ = 0;
v___x_4360_ = lean_box(v___x_4359_);
v___x_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
return v___x_4361_;
}
else
{
lean_object* v_one_4362_; lean_object* v_n_4363_; 
v_one_4362_ = lean_unsigned_to_nat(1u);
v_n_4363_ = lean_nat_sub(v_x_4345_, v_one_4362_);
lean_dec(v_x_4345_);
v_x_4344_ = v_body_4356_;
v_x_4345_ = v_n_4363_;
goto _start;
}
}
case 8:
{
lean_object* v_body_4365_; 
v_body_4365_ = lean_ctor_get(v_x_4344_, 3);
v_x_4344_ = v_body_4365_;
goto _start;
}
case 10:
{
lean_object* v_expr_4367_; 
v_expr_4367_ = lean_ctor_get(v_x_4344_, 1);
v_x_4344_ = v_expr_4367_;
goto _start;
}
default: 
{
lean_dec(v_x_4345_);
goto v___jp_4347_;
}
}
v___jp_4347_:
{
uint8_t v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = 2;
v___x_4349_ = lean_box(v___x_4348_);
v___x_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
return v___x_4350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* v_x_4369_, lean_object* v_x_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4369_, v_x_4370_);
lean_dec_ref(v_x_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* v_x_4373_, lean_object* v_x_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_x_4373_, v_x_4374_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* v_x_4381_, lean_object* v_x_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(v_x_4381_, v_x_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec_ref(v_x_4381_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* v_x_4389_, lean_object* v_x_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
switch(lean_obj_tag(v_x_4389_))
{
case 4:
{
lean_object* v_declName_4396_; lean_object* v_us_4397_; lean_object* v___x_4398_; 
v_declName_4396_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_declName_4396_);
v_us_4397_ = lean_ctor_get(v_x_4389_, 1);
lean_inc(v_us_4397_);
lean_dec_ref(v_x_4389_);
v___x_4398_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4396_, v_us_4397_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec_ref(v_a_4391_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref(v___x_4398_);
v___x_4400_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4399_, v_x_4390_);
lean_dec(v_a_4399_);
return v___x_4400_;
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_x_4390_);
v_a_4401_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4398_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4398_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_4409_; lean_object* v___x_4410_; 
v_fvarId_4409_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_fvarId_4409_);
lean_dec_ref(v_x_4389_);
v___x_4410_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4409_, v_a_4391_, v_a_4393_, v_a_4394_);
lean_dec_ref(v_a_4393_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
v___x_4412_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4411_, v_x_4390_);
lean_dec(v_a_4411_);
return v___x_4412_;
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v_x_4390_);
v_a_4413_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4410_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4410_);
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
case 2:
{
lean_object* v_mvarId_4421_; lean_object* v___x_4422_; 
v_mvarId_4421_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_mvarId_4421_);
lean_dec_ref(v_x_4389_);
v___x_4422_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4421_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec_ref(v_a_4391_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4424_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4423_);
lean_dec_ref(v___x_4422_);
v___x_4424_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4423_, v_x_4390_);
lean_dec(v_a_4423_);
return v___x_4424_;
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_x_4390_);
v_a_4425_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4422_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4422_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
case 5:
{
lean_object* v_fn_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_fn_4433_ = lean_ctor_get(v_x_4389_, 0);
lean_inc_ref(v_fn_4433_);
lean_dec_ref(v_x_4389_);
v___x_4434_ = lean_unsigned_to_nat(1u);
v___x_4435_ = lean_nat_add(v_x_4390_, v___x_4434_);
lean_dec(v_x_4390_);
v_x_4389_ = v_fn_4433_;
v_x_4390_ = v___x_4435_;
goto _start;
}
case 10:
{
lean_object* v_expr_4437_; 
v_expr_4437_ = lean_ctor_get(v_x_4389_, 1);
lean_inc_ref(v_expr_4437_);
lean_dec_ref(v_x_4389_);
v_x_4389_ = v_expr_4437_;
goto _start;
}
case 8:
{
lean_object* v_body_4439_; 
v_body_4439_ = lean_ctor_get(v_x_4389_, 3);
lean_inc_ref(v_body_4439_);
lean_dec_ref(v_x_4389_);
v_x_4389_ = v_body_4439_;
goto _start;
}
case 6:
{
lean_object* v_body_4441_; lean_object* v_zero_4442_; uint8_t v_isZero_4443_; 
v_body_4441_ = lean_ctor_get(v_x_4389_, 2);
lean_inc_ref(v_body_4441_);
lean_dec_ref(v_x_4389_);
v_zero_4442_ = lean_unsigned_to_nat(0u);
v_isZero_4443_ = lean_nat_dec_eq(v_x_4390_, v_zero_4442_);
if (v_isZero_4443_ == 1)
{
uint8_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
lean_dec_ref(v_body_4441_);
lean_dec_ref(v_a_4393_);
lean_dec_ref(v_a_4391_);
lean_dec(v_x_4390_);
v___x_4444_ = 0;
v___x_4445_ = lean_box(v___x_4444_);
v___x_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
return v___x_4446_;
}
else
{
lean_object* v_one_4447_; lean_object* v_n_4448_; 
v_one_4447_ = lean_unsigned_to_nat(1u);
v_n_4448_ = lean_nat_sub(v_x_4390_, v_one_4447_);
lean_dec(v_x_4390_);
v_x_4389_ = v_body_4441_;
v_x_4390_ = v_n_4448_;
goto _start;
}
}
default: 
{
uint8_t v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
lean_dec_ref(v_a_4393_);
lean_dec_ref(v_a_4391_);
lean_dec(v_x_4390_);
lean_dec_ref(v_x_4389_);
v___x_4450_ = 2;
v___x_4451_ = lean_box(v___x_4450_);
v___x_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
return v___x_4452_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* v_x_4453_, lean_object* v_x_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_x_4453_, v_x_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
lean_dec(v_a_4458_);
lean_dec(v_a_4456_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* v_x_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
switch(lean_obj_tag(v_x_4461_))
{
case 1:
{
lean_object* v_fvarId_4467_; lean_object* v___x_4468_; 
v_fvarId_4467_ = lean_ctor_get(v_x_4461_, 0);
lean_inc(v_fvarId_4467_);
lean_dec_ref(v_x_4461_);
v___x_4468_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(v_fvarId_4467_, v_a_4462_, v_a_4464_, v_a_4465_);
lean_dec_ref(v_a_4464_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref(v___x_4468_);
v___x_4470_ = lean_unsigned_to_nat(0u);
v___x_4471_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4469_, v___x_4470_);
lean_dec(v_a_4469_);
return v___x_4471_;
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
v_a_4472_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4468_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4468_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_4480_; lean_object* v___x_4481_; 
v_mvarId_4480_ = lean_ctor_get(v_x_4461_, 0);
lean_inc(v_mvarId_4480_);
lean_dec_ref(v_x_4461_);
v___x_4481_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(v_mvarId_4480_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_a_4462_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref(v___x_4481_);
v___x_4483_ = lean_unsigned_to_nat(0u);
v___x_4484_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4482_, v___x_4483_);
lean_dec(v_a_4482_);
return v___x_4484_;
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_a_4485_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4481_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4481_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
case 3:
{
uint8_t v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
lean_dec_ref(v_x_4461_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_a_4462_);
v___x_4493_ = 1;
v___x_4494_ = lean_box(v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
case 4:
{
lean_object* v_declName_4496_; lean_object* v_us_4497_; lean_object* v___x_4498_; 
v_declName_4496_ = lean_ctor_get(v_x_4461_, 0);
lean_inc(v_declName_4496_);
v_us_4497_ = lean_ctor_get(v_x_4461_, 1);
lean_inc(v_us_4497_);
lean_dec_ref(v_x_4461_);
v___x_4498_ = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(v_declName_4496_, v_us_4497_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_);
lean_dec_ref(v_a_4462_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref(v___x_4498_);
v___x_4500_ = lean_unsigned_to_nat(0u);
v___x_4501_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(v_a_4499_, v___x_4500_);
lean_dec(v_a_4499_);
return v___x_4501_;
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
v_a_4502_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4498_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4498_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
case 5:
{
lean_object* v_fn_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v_fn_4510_ = lean_ctor_get(v_x_4461_, 0);
lean_inc_ref(v_fn_4510_);
lean_dec_ref(v_x_4461_);
v___x_4511_ = lean_unsigned_to_nat(1u);
v___x_4512_ = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(v_fn_4510_, v___x_4511_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_);
return v___x_4512_;
}
case 6:
{
uint8_t v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
lean_dec_ref(v_x_4461_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_a_4462_);
v___x_4513_ = 0;
v___x_4514_ = lean_box(v___x_4513_);
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
return v___x_4515_;
}
case 7:
{
uint8_t v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
lean_dec_ref(v_x_4461_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_a_4462_);
v___x_4516_ = 1;
v___x_4517_ = lean_box(v___x_4516_);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
case 8:
{
lean_object* v_body_4519_; 
v_body_4519_ = lean_ctor_get(v_x_4461_, 3);
lean_inc_ref(v_body_4519_);
lean_dec_ref(v_x_4461_);
v_x_4461_ = v_body_4519_;
goto _start;
}
case 9:
{
uint8_t v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
lean_dec_ref(v_x_4461_);
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_a_4462_);
v___x_4521_ = 0;
v___x_4522_ = lean_box(v___x_4521_);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
case 10:
{
lean_object* v_expr_4524_; 
v_expr_4524_ = lean_ctor_get(v_x_4461_, 1);
lean_inc_ref(v_expr_4524_);
lean_dec_ref(v_x_4461_);
v_x_4461_ = v_expr_4524_;
goto _start;
}
default: 
{
uint8_t v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
lean_dec_ref(v_a_4464_);
lean_dec_ref(v_a_4462_);
lean_dec_ref(v_x_4461_);
v___x_4526_ = 2;
v___x_4527_ = lean_box(v___x_4526_);
v___x_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
return v___x_4528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* v_x_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Lean_Meta_isTypeQuick(v_x_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
lean_dec(v_a_4533_);
lean_dec(v_a_4531_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* v_e_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v___x_4542_; 
lean_inc_ref(v_a_4539_);
lean_inc_ref(v_a_4537_);
lean_inc_ref(v_e_4536_);
v___x_4542_ = l_Lean_Meta_isTypeQuick(v_e_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4592_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4545_ = v___x_4542_;
v_isShared_4546_ = v_isSharedCheck_4592_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4542_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4592_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
uint8_t v___x_4547_; 
v___x_4547_ = lean_unbox(v_a_4543_);
lean_dec(v_a_4543_);
switch(v___x_4547_)
{
case 0:
{
uint8_t v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec_ref(v_e_4536_);
v___x_4548_ = 0;
v___x_4549_ = lean_box(v___x_4548_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v___x_4549_);
v___x_4551_ = v___x_4545_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
case 1:
{
uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4556_; 
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec_ref(v_e_4536_);
v___x_4553_ = 1;
v___x_4554_ = lean_box(v___x_4553_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v___x_4554_);
v___x_4556_ = v___x_4545_;
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
default: 
{
lean_object* v___x_4558_; 
lean_del_object(v___x_4545_);
lean_inc(v_a_4540_);
lean_inc_ref(v_a_4539_);
lean_inc(v_a_4538_);
lean_inc_ref(v_a_4537_);
v___x_4558_ = lean_infer_type(v_e_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4560_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref(v___x_4558_);
v___x_4560_ = l_Lean_Meta_whnfD(v_a_4559_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4575_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4575_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4575_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
if (lean_obj_tag(v_a_4561_) == 3)
{
uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4568_; 
lean_dec_ref(v_a_4561_);
v___x_4565_ = 1;
v___x_4566_ = lean_box(v___x_4565_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4566_);
v___x_4568_ = v___x_4563_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
else
{
uint8_t v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4573_; 
lean_dec(v_a_4561_);
v___x_4570_ = 0;
v___x_4571_ = lean_box(v___x_4570_);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4571_);
v___x_4573_ = v___x_4563_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4571_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
v_a_4576_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4560_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4560_);
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
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
v_a_4584_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4558_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4558_);
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
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec_ref(v_e_4536_);
v_a_4593_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4542_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4542_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isType___boxed(lean_object* v_e_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l_Lean_Meta_isType(v_e_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* v_x_4608_){
_start:
{
switch(lean_obj_tag(v_x_4608_))
{
case 7:
{
lean_object* v_body_4609_; 
v_body_4609_ = lean_ctor_get(v_x_4608_, 2);
v_x_4608_ = v_body_4609_;
goto _start;
}
case 3:
{
lean_object* v_u_4611_; lean_object* v___x_4612_; 
v_u_4611_ = lean_ctor_get(v_x_4608_, 0);
lean_inc(v_u_4611_);
v___x_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4612_, 0, v_u_4611_);
return v___x_4612_;
}
default: 
{
lean_object* v___x_4613_; 
v___x_4613_ = lean_box(0);
return v___x_4613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* v_x_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_x_4614_);
lean_dec_ref(v_x_4614_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed(lean_object* v_xs_4616_, lean_object* v_body_4617_, lean_object* v_x_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(v_xs_4616_, v_body_4617_, v_x_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(lean_object* v_type_4627_, lean_object* v_xs_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
switch(lean_obj_tag(v_type_4627_))
{
case 3:
{
lean_object* v_u_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec_ref(v_xs_4628_);
v_u_4634_ = lean_ctor_get(v_type_4627_, 0);
lean_inc(v_u_4634_);
lean_dec_ref(v_type_4627_);
v___x_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4635_, 0, v_u_4634_);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
return v___x_4636_;
}
case 7:
{
lean_object* v_binderName_4637_; lean_object* v_binderType_4638_; lean_object* v_body_4639_; uint8_t v_binderInfo_4640_; lean_object* v___f_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v_binderName_4637_ = lean_ctor_get(v_type_4627_, 0);
lean_inc(v_binderName_4637_);
v_binderType_4638_ = lean_ctor_get(v_type_4627_, 1);
lean_inc_ref(v_binderType_4638_);
v_body_4639_ = lean_ctor_get(v_type_4627_, 2);
lean_inc_ref(v_body_4639_);
v_binderInfo_4640_ = lean_ctor_get_uint8(v_type_4627_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_4627_);
lean_inc_ref(v_xs_4628_);
v___f_4641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4641_, 0, v_xs_4628_);
lean_closure_set(v___f_4641_, 1, v_body_4639_);
v___x_4642_ = lean_expr_instantiate_rev(v_binderType_4638_, v_xs_4628_);
lean_dec_ref(v_xs_4628_);
lean_dec_ref(v_binderType_4638_);
v___x_4643_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4637_, v_binderInfo_4640_, v___x_4642_, v___f_4641_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
return v___x_4643_;
}
default: 
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = lean_expr_instantiate_rev(v_type_4627_, v_xs_4628_);
lean_dec_ref(v_xs_4628_);
lean_dec_ref(v_type_4627_);
lean_inc(v_a_4632_);
lean_inc_ref(v_a_4631_);
lean_inc(v_a_4630_);
lean_inc_ref(v_a_4629_);
v___x_4645_ = l_Lean_Meta_whnfD(v___x_4644_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4661_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4648_ = v___x_4645_;
v_isShared_4649_ = v_isSharedCheck_4661_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4661_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
switch(lean_obj_tag(v_a_4646_))
{
case 3:
{
lean_object* v_u_4650_; lean_object* v___x_4651_; lean_object* v___x_4653_; 
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
v_u_4650_ = lean_ctor_get(v_a_4646_, 0);
lean_inc(v_u_4650_);
lean_dec_ref(v_a_4646_);
v___x_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4651_, 0, v_u_4650_);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 0, v___x_4651_);
v___x_4653_ = v___x_4648_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4651_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
case 7:
{
lean_object* v___x_4655_; 
lean_del_object(v___x_4648_);
v___x_4655_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
v_type_4627_ = v_a_4646_;
v_xs_4628_ = v___x_4655_;
goto _start;
}
default: 
{
lean_object* v___x_4657_; lean_object* v___x_4659_; 
lean_dec(v_a_4646_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
v___x_4657_ = lean_box(0);
if (v_isShared_4649_ == 0)
{
lean_ctor_set(v___x_4648_, 0, v___x_4657_);
v___x_4659_ = v___x_4648_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
v_a_4662_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4645_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4645_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* v_xs_4670_, lean_object* v_body_4671_, lean_object* v_x_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = lean_array_push(v_xs_4670_, v_x_4672_);
v___x_4679_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_body_4671_, v___x_4678_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___boxed(lean_object* v_type_4680_, lean_object* v_xs_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4680_, v_xs_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* v_a_4688_, lean_object* v_cache_4689_, lean_object* v_a_x3f_4690_){
_start:
{
lean_object* v___x_4692_; lean_object* v_mctx_4693_; lean_object* v_zetaDeltaFVarIds_4694_; lean_object* v_postponed_4695_; lean_object* v_diag_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4706_; 
v___x_4692_ = lean_st_ref_take(v_a_4688_);
v_mctx_4693_ = lean_ctor_get(v___x_4692_, 0);
v_zetaDeltaFVarIds_4694_ = lean_ctor_get(v___x_4692_, 2);
v_postponed_4695_ = lean_ctor_get(v___x_4692_, 3);
v_diag_4696_ = lean_ctor_get(v___x_4692_, 4);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4706_ == 0)
{
lean_object* v_unused_4707_; 
v_unused_4707_ = lean_ctor_get(v___x_4692_, 1);
lean_dec(v_unused_4707_);
v___x_4698_ = v___x_4692_;
v_isShared_4699_ = v_isSharedCheck_4706_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_diag_4696_);
lean_inc(v_postponed_4695_);
lean_inc(v_zetaDeltaFVarIds_4694_);
lean_inc(v_mctx_4693_);
lean_dec(v___x_4692_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4706_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 1, v_cache_4689_);
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_mctx_4693_);
lean_ctor_set(v_reuseFailAlloc_4705_, 1, v_cache_4689_);
lean_ctor_set(v_reuseFailAlloc_4705_, 2, v_zetaDeltaFVarIds_4694_);
lean_ctor_set(v_reuseFailAlloc_4705_, 3, v_postponed_4695_);
lean_ctor_set(v_reuseFailAlloc_4705_, 4, v_diag_4696_);
v___x_4701_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4702_ = lean_st_ref_set(v_a_4688_, v___x_4701_);
v___x_4703_ = lean_box(0);
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
return v___x_4704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* v_a_4708_, lean_object* v_cache_4709_, lean_object* v_a_x3f_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4708_, v_cache_4709_, v_a_x3f_4710_);
lean_dec(v_a_x3f_4710_);
lean_dec(v_a_4708_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* v_type_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_Meta_typeFormerTypeLevelQuick(v_type_4713_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v___x_4720_; lean_object* v_cache_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4720_ = lean_st_ref_get(v_a_4715_);
v_cache_4721_ = lean_ctor_get(v___x_4720_, 1);
lean_inc_ref(v_cache_4721_);
lean_dec(v___x_4720_);
v___x_4722_ = ((lean_object*)(l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go___closed__0));
lean_inc(v_a_4715_);
v___x_4723_ = l___private_Lean_Meta_InferType_0__Lean_Meta_typeFormerTypeLevel_go(v_type_4713_, v___x_4722_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4740_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4726_ = v___x_4723_;
v_isShared_4727_ = v_isSharedCheck_4740_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4723_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4740_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
lean_inc(v_a_4724_);
if (v_isShared_4727_ == 0)
{
lean_ctor_set_tag(v___x_4726_, 1);
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
v___x_4730_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4715_, v_cache_4721_, v___x_4729_);
lean_dec_ref(v___x_4729_);
lean_dec(v_a_4715_);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4737_ == 0)
{
lean_object* v_unused_4738_; 
v_unused_4738_ = lean_ctor_get(v___x_4730_, 0);
lean_dec(v_unused_4738_);
v___x_4732_ = v___x_4730_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_dec(v___x_4730_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v_a_4724_);
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4724_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
v_a_4741_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4723_);
v___x_4742_ = lean_box(0);
v___x_4743_ = l_Lean_Meta_typeFormerTypeLevel___lam__0(v_a_4715_, v_cache_4721_, v___x_4742_);
lean_dec(v_a_4715_);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; 
v_unused_4751_ = lean_ctor_get(v___x_4743_, 0);
lean_dec(v_unused_4751_);
v___x_4745_ = v___x_4743_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_dec(v___x_4743_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
lean_ctor_set_tag(v___x_4745_, 1);
lean_ctor_set(v___x_4745_, 0, v_a_4741_);
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4741_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
else
{
lean_object* v___x_4752_; 
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec_ref(v_type_4713_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4719_);
return v___x_4752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___boxed(lean_object* v_type_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_){
_start:
{
lean_object* v_res_4759_; 
v_res_4759_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* v_type_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4781_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4769_ = v___x_4766_;
v_isShared_4770_ = v_isSharedCheck_4781_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4781_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
if (lean_obj_tag(v_a_4767_) == 0)
{
uint8_t v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4771_ = 0;
v___x_4772_ = lean_box(v___x_4771_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 0, v___x_4772_);
v___x_4774_ = v___x_4769_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
else
{
uint8_t v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
lean_dec_ref(v_a_4767_);
v___x_4776_ = 1;
v___x_4777_ = lean_box(v___x_4776_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 0, v___x_4777_);
v___x_4779_ = v___x_4769_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
v_a_4782_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4766_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4766_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType___boxed(lean_object* v_type_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_Lean_Meta_isTypeFormerType(v_type_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
return v_res_4796_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(lean_object* v_x_4797_, lean_object* v_x_4798_){
_start:
{
if (lean_obj_tag(v_x_4797_) == 0)
{
if (lean_obj_tag(v_x_4798_) == 0)
{
uint8_t v___x_4799_; 
v___x_4799_ = 1;
return v___x_4799_;
}
else
{
uint8_t v___x_4800_; 
v___x_4800_ = 0;
return v___x_4800_;
}
}
else
{
if (lean_obj_tag(v_x_4798_) == 0)
{
uint8_t v___x_4801_; 
v___x_4801_ = 0;
return v___x_4801_;
}
else
{
lean_object* v_val_4802_; lean_object* v_val_4803_; uint8_t v___x_4804_; 
v_val_4802_ = lean_ctor_get(v_x_4797_, 0);
v_val_4803_ = lean_ctor_get(v_x_4798_, 0);
v___x_4804_ = lean_level_eq(v_val_4802_, v_val_4803_);
return v___x_4804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* v_x_4805_, lean_object* v_x_4806_){
_start:
{
uint8_t v_res_4807_; lean_object* v_r_4808_; 
v_res_4807_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_x_4805_, v_x_4806_);
lean_dec(v_x_4806_);
lean_dec(v_x_4805_);
v_r_4808_ = lean_box(v_res_4807_);
return v_r_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* v_type_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_Lean_Meta_typeFormerTypeLevel(v_type_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4828_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; uint8_t v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4826_; 
v___x_4822_ = ((lean_object*)(l_Lean_Meta_isPropFormerType___closed__0));
v___x_4823_ = l_Option_instBEq_beq___at___00Lean_Meta_isPropFormerType_spec__0(v_a_4818_, v___x_4822_);
lean_dec(v_a_4818_);
v___x_4824_ = lean_box(v___x_4823_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v___x_4824_);
v___x_4826_ = v___x_4820_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4824_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
v_a_4829_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4817_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4817_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType___boxed(lean_object* v_type_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Lean_Meta_isPropFormerType(v_type_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* v_e_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
lean_object* v___x_4850_; 
lean_inc(v_a_4848_);
lean_inc_ref(v_a_4847_);
lean_inc(v_a_4846_);
lean_inc_ref(v_a_4845_);
v___x_4850_ = lean_infer_type(v_e_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4852_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref(v___x_4850_);
v___x_4852_ = l_Lean_Meta_isTypeFormerType(v_a_4851_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
return v___x_4852_;
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
v_a_4853_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4850_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4850_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer___boxed(lean_object* v_e_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l_Lean_Meta_isTypeFormer(v_e_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(lean_object* v_type_4868_, lean_object* v_maxFVars_x3f_4869_, lean_object* v_k_4870_, uint8_t v_cleanupAnnotations_4871_, uint8_t v_whnfType_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v___f_4878_; lean_object* v___x_4879_; 
v___f_4878_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4878_, 0, v_k_4870_);
v___x_4879_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4868_, v_maxFVars_x3f_4869_, v___f_4878_, v_cleanupAnnotations_4871_, v_whnfType_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4879_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4879_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
else
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
v_a_4888_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4879_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4879_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg___boxed(lean_object* v_type_4896_, lean_object* v_maxFVars_x3f_4897_, lean_object* v_k_4898_, lean_object* v_cleanupAnnotations_4899_, lean_object* v_whnfType_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4906_; uint8_t v_whnfType_boxed_4907_; lean_object* v_res_4908_; 
v_cleanupAnnotations_boxed_4906_ = lean_unbox(v_cleanupAnnotations_4899_);
v_whnfType_boxed_4907_ = lean_unbox(v_whnfType_4900_);
v_res_4908_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4896_, v_maxFVars_x3f_4897_, v_k_4898_, v_cleanupAnnotations_boxed_4906_, v_whnfType_boxed_4907_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(lean_object* v_00_u03b1_4909_, lean_object* v_type_4910_, lean_object* v_maxFVars_x3f_4911_, lean_object* v_k_4912_, uint8_t v_cleanupAnnotations_4913_, uint8_t v_whnfType_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_4910_, v_maxFVars_x3f_4911_, v_k_4912_, v_cleanupAnnotations_4913_, v_whnfType_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* v_00_u03b1_4921_, lean_object* v_type_4922_, lean_object* v_maxFVars_x3f_4923_, lean_object* v_k_4924_, lean_object* v_cleanupAnnotations_4925_, lean_object* v_whnfType_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4932_; uint8_t v_whnfType_boxed_4933_; lean_object* v_res_4934_; 
v_cleanupAnnotations_boxed_4932_ = lean_unbox(v_cleanupAnnotations_4925_);
v_whnfType_boxed_4933_ = lean_unbox(v_whnfType_4926_);
v_res_4934_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4(v_00_u03b1_4921_, v_type_4922_, v_maxFVars_x3f_4923_, v_k_4924_, v_cleanupAnnotations_boxed_4932_, v_whnfType_boxed_4933_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
return v_res_4934_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* v_a_4935_, lean_object* v_as_4936_, size_t v_i_4937_, size_t v_stop_4938_){
_start:
{
uint8_t v___x_4939_; 
v___x_4939_ = lean_usize_dec_eq(v_i_4937_, v_stop_4938_);
if (v___x_4939_ == 0)
{
lean_object* v___x_4940_; uint8_t v___x_4941_; 
v___x_4940_ = lean_array_uget_borrowed(v_as_4936_, v_i_4937_);
v___x_4941_ = lean_expr_eqv(v_a_4935_, v___x_4940_);
if (v___x_4941_ == 0)
{
size_t v___x_4942_; size_t v___x_4943_; 
v___x_4942_ = ((size_t)1ULL);
v___x_4943_ = lean_usize_add(v_i_4937_, v___x_4942_);
v_i_4937_ = v___x_4943_;
goto _start;
}
else
{
return v___x_4941_;
}
}
else
{
uint8_t v___x_4945_; 
v___x_4945_ = 0;
return v___x_4945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* v_a_4946_, lean_object* v_as_4947_, lean_object* v_i_4948_, lean_object* v_stop_4949_){
_start:
{
size_t v_i_boxed_4950_; size_t v_stop_boxed_4951_; uint8_t v_res_4952_; lean_object* v_r_4953_; 
v_i_boxed_4950_ = lean_unbox_usize(v_i_4948_);
lean_dec(v_i_4948_);
v_stop_boxed_4951_ = lean_unbox_usize(v_stop_4949_);
lean_dec(v_stop_4949_);
v_res_4952_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4946_, v_as_4947_, v_i_boxed_4950_, v_stop_boxed_4951_);
lean_dec_ref(v_as_4947_);
lean_dec_ref(v_a_4946_);
v_r_4953_ = lean_box(v_res_4952_);
return v_r_4953_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(lean_object* v_as_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; uint8_t v___x_4958_; 
v___x_4956_ = lean_unsigned_to_nat(0u);
v___x_4957_ = lean_array_get_size(v_as_4954_);
v___x_4958_ = lean_nat_dec_lt(v___x_4956_, v___x_4957_);
if (v___x_4958_ == 0)
{
return v___x_4958_;
}
else
{
if (v___x_4958_ == 0)
{
return v___x_4958_;
}
else
{
size_t v___x_4959_; size_t v___x_4960_; uint8_t v___x_4961_; 
v___x_4959_ = ((size_t)0ULL);
v___x_4960_ = lean_usize_of_nat(v___x_4957_);
v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0_spec__0(v_a_4955_, v_as_4954_, v___x_4959_, v___x_4960_);
return v___x_4961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* v_as_4962_, lean_object* v_a_4963_){
_start:
{
uint8_t v_res_4964_; lean_object* v_r_4965_; 
v_res_4964_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_as_4962_, v_a_4963_);
lean_dec_ref(v_a_4963_);
lean_dec_ref(v_as_4962_);
v_r_4965_ = lean_box(v_res_4964_);
return v_r_4965_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(lean_object* v_xs_4966_, lean_object* v_e_4967_){
_start:
{
uint8_t v___x_4968_; lean_object* v_d_4970_; lean_object* v_b_4971_; 
v___x_4968_ = l_Lean_Expr_hasFVar(v_e_4967_);
if (v___x_4968_ == 0)
{
lean_dec_ref(v_e_4967_);
return v___x_4968_;
}
else
{
switch(lean_obj_tag(v_e_4967_))
{
case 7:
{
lean_object* v_binderType_4974_; lean_object* v_body_4975_; 
v_binderType_4974_ = lean_ctor_get(v_e_4967_, 1);
lean_inc_ref(v_binderType_4974_);
v_body_4975_ = lean_ctor_get(v_e_4967_, 2);
lean_inc_ref(v_body_4975_);
lean_dec_ref(v_e_4967_);
v_d_4970_ = v_binderType_4974_;
v_b_4971_ = v_body_4975_;
goto v___jp_4969_;
}
case 6:
{
lean_object* v_binderType_4976_; lean_object* v_body_4977_; 
v_binderType_4976_ = lean_ctor_get(v_e_4967_, 1);
lean_inc_ref(v_binderType_4976_);
v_body_4977_ = lean_ctor_get(v_e_4967_, 2);
lean_inc_ref(v_body_4977_);
lean_dec_ref(v_e_4967_);
v_d_4970_ = v_binderType_4976_;
v_b_4971_ = v_body_4977_;
goto v___jp_4969_;
}
case 10:
{
lean_object* v_expr_4978_; 
v_expr_4978_ = lean_ctor_get(v_e_4967_, 1);
lean_inc_ref(v_expr_4978_);
lean_dec_ref(v_e_4967_);
v_e_4967_ = v_expr_4978_;
goto _start;
}
case 8:
{
lean_object* v_type_4980_; lean_object* v_value_4981_; lean_object* v_body_4982_; uint8_t v___x_4983_; 
v_type_4980_ = lean_ctor_get(v_e_4967_, 1);
lean_inc_ref(v_type_4980_);
v_value_4981_ = lean_ctor_get(v_e_4967_, 2);
lean_inc_ref(v_value_4981_);
v_body_4982_ = lean_ctor_get(v_e_4967_, 3);
lean_inc_ref(v_body_4982_);
lean_dec_ref(v_e_4967_);
v___x_4983_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4966_, v_type_4980_);
if (v___x_4983_ == 0)
{
uint8_t v___x_4984_; 
v___x_4984_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4966_, v_value_4981_);
if (v___x_4984_ == 0)
{
v_e_4967_ = v_body_4982_;
goto _start;
}
else
{
lean_dec_ref(v_body_4982_);
return v___x_4968_;
}
}
else
{
lean_dec_ref(v_body_4982_);
lean_dec_ref(v_value_4981_);
return v___x_4968_;
}
}
case 5:
{
lean_object* v_fn_4986_; lean_object* v_arg_4987_; uint8_t v___x_4988_; 
v_fn_4986_ = lean_ctor_get(v_e_4967_, 0);
lean_inc_ref(v_fn_4986_);
v_arg_4987_ = lean_ctor_get(v_e_4967_, 1);
lean_inc_ref(v_arg_4987_);
lean_dec_ref(v_e_4967_);
v___x_4988_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4966_, v_fn_4986_);
if (v___x_4988_ == 0)
{
v_e_4967_ = v_arg_4987_;
goto _start;
}
else
{
lean_dec_ref(v_arg_4987_);
return v___x_4968_;
}
}
case 11:
{
lean_object* v_struct_4990_; 
v_struct_4990_ = lean_ctor_get(v_e_4967_, 2);
lean_inc_ref(v_struct_4990_);
lean_dec_ref(v_e_4967_);
v_e_4967_ = v_struct_4990_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4992_; lean_object* v___x_4993_; uint8_t v___x_4994_; 
v_fvarId_4992_ = lean_ctor_get(v_e_4967_, 0);
lean_inc(v_fvarId_4992_);
lean_dec_ref(v_e_4967_);
v___x_4993_ = l_Lean_Expr_fvar___override(v_fvarId_4992_);
v___x_4994_ = l_Array_contains___at___00Lean_Meta_arrowDomainsN_spec__0(v_xs_4966_, v___x_4993_);
lean_dec_ref(v___x_4993_);
return v___x_4994_;
}
default: 
{
uint8_t v___x_4995_; 
lean_dec_ref(v_e_4967_);
v___x_4995_ = 0;
return v___x_4995_;
}
}
}
v___jp_4969_:
{
uint8_t v___x_4972_; 
v___x_4972_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4966_, v_d_4970_);
if (v___x_4972_ == 0)
{
v_e_4967_ = v_b_4971_;
goto _start;
}
else
{
lean_dec_ref(v_b_4971_);
return v___x_4968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* v_xs_4996_, lean_object* v_e_4997_){
_start:
{
uint8_t v_res_4998_; lean_object* v_r_4999_; 
v_res_4998_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_4996_, v_e_4997_);
lean_dec_ref(v_xs_4996_);
v_r_4999_ = lean_box(v_res_4998_);
return v_r_4999_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__0));
v___x_5002_ = l_Lean_stringToMessageData(v___x_5001_);
return v___x_5002_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__2));
v___x_5005_ = l_Lean_stringToMessageData(v___x_5004_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(lean_object* v_xs_5006_, lean_object* v_type_5007_, lean_object* v_as_5008_, size_t v_sz_5009_, size_t v_i_5010_, lean_object* v_b_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v_a_5018_; uint8_t v___x_5022_; 
v___x_5022_ = lean_usize_dec_lt(v_i_5010_, v_sz_5009_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; 
lean_dec_ref(v_type_5007_);
v___x_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5023_, 0, v_b_5011_);
return v___x_5023_;
}
else
{
lean_object* v___x_5024_; lean_object* v_a_5025_; uint8_t v___x_5026_; 
v___x_5024_ = lean_box(0);
v_a_5025_ = lean_array_uget_borrowed(v_as_5008_, v_i_5010_);
lean_inc(v_a_5025_);
v___x_5026_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_arrowDomainsN_spec__2(v_xs_5006_, v_a_5025_);
if (v___x_5026_ == 0)
{
v_a_5018_ = v___x_5024_;
goto v___jp_5017_;
}
else
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__1);
lean_inc(v_a_5025_);
v___x_5028_ = l_Lean_MessageData_ofExpr(v_a_5025_);
v___x_5029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5027_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
v___x_5030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___closed__3);
v___x_5031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5029_);
lean_ctor_set(v___x_5031_, 1, v___x_5030_);
lean_inc_ref(v_type_5007_);
v___x_5032_ = l_Lean_MessageData_ofExpr(v_type_5007_);
v___x_5033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5031_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5033_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_dec_ref(v___x_5034_);
v_a_5018_ = v___x_5024_;
goto v___jp_5017_;
}
else
{
lean_dec_ref(v_type_5007_);
return v___x_5034_;
}
}
}
v___jp_5017_:
{
size_t v___x_5019_; size_t v___x_5020_; 
v___x_5019_ = ((size_t)1ULL);
v___x_5020_ = lean_usize_add(v_i_5010_, v___x_5019_);
v_i_5010_ = v___x_5020_;
v_b_5011_ = v_a_5018_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* v_xs_5035_, lean_object* v_type_5036_, lean_object* v_as_5037_, lean_object* v_sz_5038_, lean_object* v_i_5039_, lean_object* v_b_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
size_t v_sz_boxed_5046_; size_t v_i_boxed_5047_; lean_object* v_res_5048_; 
v_sz_boxed_5046_ = lean_unbox_usize(v_sz_5038_);
lean_dec(v_sz_5038_);
v_i_boxed_5047_ = lean_unbox_usize(v_i_5039_);
lean_dec(v_i_5039_);
v_res_5048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5035_, v_type_5036_, v_as_5037_, v_sz_boxed_5046_, v_i_boxed_5047_, v_b_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec_ref(v_as_5037_);
lean_dec_ref(v_xs_5035_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(size_t v_sz_5049_, size_t v_i_5050_, lean_object* v_bs_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
uint8_t v___x_5057_; 
v___x_5057_ = lean_usize_dec_lt(v_i_5050_, v_sz_5049_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; 
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
v___x_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5058_, 0, v_bs_5051_);
return v___x_5058_;
}
else
{
lean_object* v_v_5059_; lean_object* v___x_5060_; 
v_v_5059_ = lean_array_uget_borrowed(v_bs_5051_, v_i_5050_);
lean_inc(v___y_5055_);
lean_inc_ref(v___y_5054_);
lean_inc(v___y_5053_);
lean_inc_ref(v___y_5052_);
lean_inc(v_v_5059_);
v___x_5060_ = lean_infer_type(v_v_5059_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5062_; lean_object* v_bs_x27_5063_; size_t v___x_5064_; size_t v___x_5065_; lean_object* v___x_5066_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref(v___x_5060_);
v___x_5062_ = lean_unsigned_to_nat(0u);
v_bs_x27_5063_ = lean_array_uset(v_bs_5051_, v_i_5050_, v___x_5062_);
v___x_5064_ = ((size_t)1ULL);
v___x_5065_ = lean_usize_add(v_i_5050_, v___x_5064_);
v___x_5066_ = lean_array_uset(v_bs_x27_5063_, v_i_5050_, v_a_5061_);
v_i_5050_ = v___x_5065_;
v_bs_5051_ = v___x_5066_;
goto _start;
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec_ref(v_bs_5051_);
v_a_5068_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5060_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5060_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1___boxed(lean_object* v_sz_5076_, lean_object* v_i_5077_, lean_object* v_bs_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
size_t v_sz_boxed_5084_; size_t v_i_boxed_5085_; lean_object* v_res_5086_; 
v_sz_boxed_5084_ = lean_unbox_usize(v_sz_5076_);
lean_dec(v_sz_5076_);
v_i_boxed_5085_ = lean_unbox_usize(v_i_5077_);
lean_dec(v_i_5077_);
v_res_5086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_boxed_5084_, v_i_boxed_5085_, v_bs_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
return v_res_5086_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5088_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__0));
v___x_5089_ = l_Lean_stringToMessageData(v___x_5088_);
return v___x_5089_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5091_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__2));
v___x_5092_ = l_Lean_stringToMessageData(v___x_5091_);
return v___x_5092_;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5094_ = ((lean_object*)(l_Lean_Meta_arrowDomainsN___lam__0___closed__4));
v___x_5095_ = l_Lean_stringToMessageData(v___x_5094_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* v_type_5096_, lean_object* v_n_5097_, lean_object* v_xs_5098_, lean_object* v_x_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
lean_object* v___x_5129_; uint8_t v___x_5130_; 
v___x_5129_ = lean_array_get_size(v_xs_5098_);
v___x_5130_ = lean_nat_dec_eq(v___x_5129_, v_n_5097_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec_ref(v_xs_5098_);
v___x_5131_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__1, &l_Lean_Meta_arrowDomainsN___lam__0___closed__1_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
v___x_5132_ = l_Lean_MessageData_ofExpr(v_type_5096_);
v___x_5133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5131_);
lean_ctor_set(v___x_5133_, 1, v___x_5132_);
v___x_5134_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__3, &l_Lean_Meta_arrowDomainsN___lam__0___closed__3_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
v___x_5135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5133_);
lean_ctor_set(v___x_5135_, 1, v___x_5134_);
v___x_5136_ = l_Nat_reprFast(v_n_5097_);
v___x_5137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
v___x_5138_ = l_Lean_MessageData_ofFormat(v___x_5137_);
v___x_5139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5139_, 0, v___x_5135_);
lean_ctor_set(v___x_5139_, 1, v___x_5138_);
v___x_5140_ = lean_obj_once(&l_Lean_Meta_arrowDomainsN___lam__0___closed__5, &l_Lean_Meta_arrowDomainsN___lam__0___closed__5_once, _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
v___x_5141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = l_Lean_throwError___at___00Lean_Meta_throwFunctionExpected_spec__0___redArg(v___x_5141_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5142_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5142_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
else
{
lean_dec(v_n_5097_);
goto v___jp_5105_;
}
v___jp_5105_:
{
size_t v_sz_5106_; size_t v___x_5107_; lean_object* v___x_5108_; 
v_sz_5106_ = lean_array_size(v_xs_5098_);
v___x_5107_ = ((size_t)0ULL);
lean_inc(v___y_5103_);
lean_inc_ref(v___y_5102_);
lean_inc(v___y_5101_);
lean_inc_ref(v___y_5100_);
lean_inc_ref(v_xs_5098_);
v___x_5108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_arrowDomainsN_spec__1(v_sz_5106_, v___x_5107_, v_xs_5098_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5110_; size_t v_sz_5111_; lean_object* v___x_5112_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref(v___x_5108_);
v___x_5110_ = lean_box(0);
v_sz_5111_ = lean_array_size(v_a_5109_);
v___x_5112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_arrowDomainsN_spec__3(v_xs_5098_, v_type_5096_, v_a_5109_, v_sz_5111_, v___x_5107_, v___x_5110_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_xs_5098_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
v_isSharedCheck_5119_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5119_ == 0)
{
lean_object* v_unused_5120_; 
v_unused_5120_ = lean_ctor_get(v___x_5112_, 0);
lean_dec(v_unused_5120_);
v___x_5114_ = v___x_5112_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_dec(v___x_5112_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
lean_ctor_set(v___x_5114_, 0, v_a_5109_);
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5109_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_dec(v_a_5109_);
v_a_5121_ = lean_ctor_get(v___x_5112_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5112_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5112_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
else
{
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
lean_dec_ref(v_xs_5098_);
lean_dec_ref(v_type_5096_);
return v___x_5108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* v_type_5151_, lean_object* v_n_5152_, lean_object* v_xs_5153_, lean_object* v_x_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Lean_Meta_arrowDomainsN___lam__0(v_type_5151_, v_n_5152_, v_xs_5153_, v_x_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
lean_dec_ref(v_x_5154_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* v_n_5161_, lean_object* v_type_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v___f_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; lean_object* v___x_5171_; 
lean_inc(v_n_5161_);
lean_inc_ref(v_type_5162_);
v___f_5168_ = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5168_, 0, v_type_5162_);
lean_closure_set(v___f_5168_, 1, v_n_5161_);
v___x_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5169_, 0, v_n_5161_);
v___x_5170_ = 0;
v___x_5171_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_arrowDomainsN_spec__4___redArg(v_type_5162_, v___x_5169_, v___f_5168_, v___x_5170_, v___x_5170_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___boxed(lean_object* v_n_5172_, lean_object* v_type_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Lean_Meta_arrowDomainsN(v_n_5172_, v_type_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* v_n_5180_, lean_object* v_e_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v___x_5187_; 
lean_inc(v_a_5185_);
lean_inc_ref(v_a_5184_);
lean_inc(v_a_5183_);
lean_inc_ref(v_a_5182_);
v___x_5187_ = lean_infer_type(v_e_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5189_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5188_);
lean_dec_ref(v___x_5187_);
v___x_5189_ = l_Lean_Meta_arrowDomainsN(v_n_5180_, v_a_5188_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
return v___x_5189_;
}
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
lean_dec(v_a_5185_);
lean_dec_ref(v_a_5184_);
lean_dec(v_a_5183_);
lean_dec_ref(v_a_5182_);
lean_dec(v_n_5180_);
v_a_5190_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5187_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5187_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object* v_n_5198_, lean_object* v_e_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l_Lean_Meta_inferArgumentTypesN(v_n_5198_, v_e_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_);
return v_res_5205_;
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
